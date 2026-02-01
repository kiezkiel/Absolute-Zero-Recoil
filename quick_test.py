# PUBG_REALTIME_MEGA_PRO_SCOPE_DETECTOR.py
from ultralytics import YOLO
import cv2
import numpy as np
import win32api
import time
import mss
import base64
from flask import Flask, render_template_string, jsonify, request
import threading
import winsound
import os
import glob
import json
from datetime import datetime
import pandas as pd
from collections import defaultdict, deque
import hashlib
from io import BytesIO
from PIL import Image
import webbrowser
import socket  # Add this at the top with other imports

# ============================================================================
# MEGA MAPPING CLASSES (From advanced mapping code)
# ============================================================================
import json
import numpy as np

class NumpyEncoder(json.JSONEncoder):
    """Custom JSON encoder for numpy types"""
    def default(self, obj):
        if isinstance(obj, np.integer):
            return int(obj)
        elif isinstance(obj, np.floating):
            return float(obj)
        elif isinstance(obj, np.ndarray):
            return obj.tolist()
        elif isinstance(obj, np.generic):
            return obj.item()
        else:
            return super().default(obj)
class MEGASlotTracker:
    """MEGA-PRO slot tracker with ALL 10 improvements implemented"""
    
    def __init__(self, max_track_frames=10):
        # Core tracking data
        self.slot_regions = {}
        self.weapon_positions = {}
        self.scope_positions = {}
        self.distance_log = []
        self.mapping_history = defaultdict(lambda: deque(maxlen=20))
        
        # Video tracking
        self.tracked_slots = {}
        self.frame_buffer = deque(maxlen=max_track_frames)
        self.weapon_tracks = {}
        
        # Statistics for analysis
        self.performance_stats = {
            'total_mappings': 0,
            'successful_mappings': 0,
            'failed_mappings': 0,
            'scope_mappings': 0,
            'scope_success': 0,
            'distance_distribution': [],
            'confidence_distribution': [],
            'slot_hit_rates': defaultdict(lambda: {'hits': 0, 'misses': 0})
        }
        
        # Configuration
        self.config = {
            'distance_threshold': 0.3,  # 30% of image width
            'iou_threshold': 0.1,
            'confidence_threshold': 0.35,
            'scope_distance_threshold': 0.15,  # Scopes are closer to weapons
            'region_expansion': {
                'horizontal': 0.2,
                'vertical_top': 0.3,
                'vertical_bottom': 0.15
            },
            'weights': {
                'distance': 0.25,
                'iou': 0.20,
                'confidence': 0.25,
                'alignment': 0.15,
                'size_ratio': 0.10,
                'temporal': 0.05
            },
            'scope_weights': {
                'vertical_alignment': 0.35,  # Scope should be above weapon
                'horizontal_alignment': 0.30,
                'distance': 0.20,
                'size_ratio': 0.15  # Scope smaller than weapon
            }
        }
    
    # 1️⃣ Regional Slot Tracking with IoU
    def define_slot_regions_with_iou(self, slots, image_shape):
        """Enhanced region definition with IoU tracking"""
        h, w = image_shape[:2]
        slot_regions = {}
        
        for slot in slots:
            x1, y1, x2, y2 = slot['bbox']
            
            # Dynamic expansion based on slot size
            slot_width = x2 - x1
            slot_height = y2 - y1
            
            expanded_x1 = max(0, x1 - slot_width * self.config['region_expansion']['horizontal'])
            expanded_y1 = max(0, y1 - slot_height * self.config['region_expansion']['vertical_top'])
            expanded_x2 = min(w, x2 + slot_width * self.config['region_expansion']['horizontal'])
            expanded_y2 = min(h, y2 + slot_height * self.config['region_expansion']['vertical_bottom'])
            
            slot_regions[slot['class']] = {
                'original': (x1, y1, x2, y2),
                'expanded': (expanded_x1, expanded_y1, expanded_x2, expanded_y2),
                'center': ((x1 + x2) / 2, (y1 + y2) / 2),
                'area': slot_width * slot_height,
                'confidence': slot['confidence'],
                'iou_ready': True  # Flag for IoU calculations
            }
        
        return slot_regions
    
    # 🔍 FIXED: Scope to Weapon Mapping with SLOT CONTAINMENT
    def map_scopes_to_weapons_with_distance_fallback(self, scopes, weapons, image_shape, weapon_slot_mapping):
        """
        Enhanced scope mapping with distance-based tie-breaking.
        """
        scope_weapon_mapping = {}
        scope_slot_mapping = {}

        if not scopes or not weapons:
            return scope_weapon_mapping, scope_slot_mapping

        # 🔧 NEW: Track all candidate mappings by weapon
        weapon_candidates = {}  # weapon_name -> [(scope, score, distance)]

        # First pass: Find ALL possible scope-weapon matches within slots
        for scope in scopes:
            s_center = self.get_center(scope['bbox'])

            for weapon in weapons:
                weapon_slot = weapon_slot_mapping.get(weapon['class'])
                if not weapon_slot or weapon_slot == "No slot":
                    continue

                w_center = self.get_center(weapon['bbox'])

                # Calculate distances
                dx = abs(w_center[0] - s_center[0])
                dy = w_center[1] - s_center[1]  # positive if weapon is BELOW scope

                # Quick distance check (must be in same slot area)
                if not (0 < dy < 100 and dx < 80):  # Basic same-slot check
                    continue

                # Calculate score
                score = self.calculate_scope_weapon_score(scope, weapon, dx, dy)

                if score > 0.3:  # Minimum threshold
                    if weapon['class'] not in weapon_candidates:
                        weapon_candidates[weapon['class']] = []
                    weapon_candidates[weapon['class']].append({
                        'scope': scope,
                        'score': score,
                        'distance': dy,  # Use vertical distance for tie-breaking
                        'dx': dx,
                        'dy': dy
                    })

        # 🔧 NEW: Resolve conflicts - if multiple scopes map to same weapon, pick the closest one
        for weapon_name, candidates in weapon_candidates.items():
            if len(candidates) == 1:
                # Only one candidate - assign it
                candidate = candidates[0]
                scope_name = candidate['scope']['class']
                scope_weapon_mapping[scope_name] = {
                    'weapon': weapon_name,
                    'score': candidate['score'],
                    'distance': candidate['distance']
                }
                scope_slot_mapping[scope_name] = weapon_slot_mapping[weapon_name]
            else:
                # Multiple scopes want the same weapon - pick the closest one
                print(f"   🔍 Multiple scopes competing for {weapon_name}:")
                for i, candidate in enumerate(candidates):
                    print(f"      {i+1}. {candidate['scope']['class']}: score={candidate['score']:.2f}, dy={candidate['dy']:.1f}px")

                # Sort by distance (closest first), then by score
                candidates_sorted = sorted(candidates, 
                                          key=lambda x: (x['dy'], -x['score']))  # Lower dy = closer

                # Assign the closest scope
                best_candidate = candidates_sorted[0]
                scope_name = best_candidate['scope']['class']
                scope_weapon_mapping[scope_name] = {
                    'weapon': weapon_name,
                    'score': best_candidate['score'],
                    'distance': best_candidate['distance']
                }
                scope_slot_mapping[scope_name] = weapon_slot_mapping[weapon_name]

        return scope_weapon_mapping, scope_slot_mapping

    def calculate_scope_weapon_score(self, scope, weapon, dx, dy):
        """Calculate score between scope and weapon"""
        score = 0.0

        # Your measured distances
        PREFERRED_VERTICAL = 44
        PREFERRED_HORIZONTAL = 29

        # Vertical score (50% weight)
        vertical_error = abs(dy - PREFERRED_VERTICAL)
        vertical_score = max(0, 1 - vertical_error / 80)  # Max 80px error
        score += vertical_score * 0.5

        # Horizontal score (30% weight)
        horizontal_error = abs(dx - PREFERRED_HORIZONTAL)
        horizontal_score = max(0, 1 - horizontal_error / 60)  # Max 60px error
        score += horizontal_score * 0.3

        # IoU bonus (15% weight)
        iou = self.calculate_iou(scope['bbox'], weapon['bbox'])
        if iou > 0:
            score += iou * 0.15

        # Size ratio check (5% weight)
        scope_area = self.calculate_area(scope['bbox'])
        weapon_area = self.calculate_area(weapon['bbox'])
        if scope_area < weapon_area * 0.8:  # Scope should be smaller
            score += 0.05

        return score
    
    def add_scope_distance_debug(self, debug_img, scope, weapon, mapping_info):
        """Add visual debug info for scope-weapon distances"""
        if not scope or not weapon:
            return

        s_center = self.get_center(scope['bbox'])
        w_center = self.get_center(weapon['bbox'])

        s_center_int = tuple(map(int, s_center))
        w_center_int = tuple(map(int, w_center))

        # Draw distance lines
        cv2.line(debug_img, s_center_int, (w_center_int[0], s_center_int[1]), (0, 255, 255), 1)  # Horizontal line
        cv2.line(debug_img, (w_center_int[0], s_center_int[1]), w_center_int, (0, 255, 255), 1)  # Vertical line

        # Calculate distances
        dx = abs(w_center[0] - s_center[0])
        dy = w_center[1] - s_center[1]

        # Draw distance text
        cv2.putText(debug_img, f"dy: {dy:.0f}px", 
                   (w_center_int[0] + 10, (s_center_int[1] + w_center_int[1]) // 2),
                   cv2.FONT_HERSHEY_SIMPLEX, 0.4, (0, 255, 255), 1)
        cv2.putText(debug_img, f"dx: {dx:.0f}px",
                   ((s_center_int[0] + w_center_int[0]) // 2, s_center_int[1] - 5),
                   cv2.FONT_HERSHEY_SIMPLEX, 0.4, (0, 255, 255), 1)

        # Draw target distance indicators
        target_y = w_center_int[1] - 44  # 44px above weapon
        cv2.line(debug_img, (w_center_int[0] - 5, target_y), (w_center_int[0] + 5, target_y), 
                (0, 255, 0), 2)  # Green target line
        cv2.putText(debug_img, "44px target", (w_center_int[0] + 10, target_y),
                   cv2.FONT_HERSHEY_SIMPLEX, 0.4, (0, 255, 0), 1)
    
    # 3️⃣ Weighted Multi-Factor Mapping (Enhanced)
    def weighted_slot_mapping_mega(self, weapon, available_slots, image_shape, frame_id=None):
        """MEGA weighted mapping with all factors"""
        if not available_slots:
            return None, 0.0, {}
        
        weapon_center = self.get_center(weapon['bbox'])
        weapon_area = self.calculate_area(weapon['bbox'])
        weapon_conf = weapon['confidence']
        
        detailed_scores = {}
        
        for slot in available_slots:
            slot_center = self.get_center(slot['bbox'])
            slot_area = self.calculate_area(slot['bbox'])
            slot_conf = slot['confidence']
            
            # Calculate all factors
            factors = {}
            
            # Distance factor (normalized)
            dist = self.calculate_distance(weapon_center, slot_center)
            max_possible_dist = np.sqrt(image_shape[0]**2 + image_shape[1]**2)
            factors['distance'] = max(0, 1 - (dist / (image_shape[1] * 0.4)))
            
            # IoU factor (if regions available)
            factors['iou'] = self.calculate_iou(weapon['bbox'], slot['bbox'])
            
            # Confidence factor (combined)
            factors['confidence'] = (weapon_conf + slot_conf) / 2
            
            # X-alignment factor (same column)
            x_align = 1 - abs(weapon_center[0] - slot_center[0]) / (image_shape[1] * 0.25)
            factors['alignment'] = max(0, min(1, x_align))
            
            # Size ratio factor (weapon should be larger)
            size_ratio = weapon_area / max(slot_area, 1)
            factors['size_ratio'] = min(1, size_ratio / 15)
            
            # Temporal factor (if previous frames)
            if frame_id and weapon['class'] in self.mapping_history:
                temporal_score = self.calculate_temporal_score(
                    weapon['class'], slot['class'], frame_id
                )
                factors['temporal'] = temporal_score
            else:
                factors['temporal'] = 0.5  # Neutral
            
            # Weighted total score
            total_score = sum(
                factors[factor] * self.config['weights'][factor] 
                for factor in self.config['weights']
                if factor in factors
            )
            
            detailed_scores[slot['class']] = {
                'score': total_score,
                'factors': factors,
                'distance': dist,
                'normalized_distance': dist / image_shape[1]
            }
        
        # Find best match
        if detailed_scores:
            best_slot = max(detailed_scores.items(), key=lambda x: x[1]['score'])
            slot_name, score_data = best_slot
            
            # Enhanced thresholding with multiple conditions
            passes_threshold = (
                score_data['score'] >= self.config['confidence_threshold'] and
                score_data['normalized_distance'] < self.config['distance_threshold'] and
                score_data['factors']['iou'] >= self.config['iou_threshold']
            )
            
            if passes_threshold:
                return slot_name, score_data['score'], score_data
        
        return None, 0.0, {}
    
    # 4️⃣ Temporal Tracking (for video)
    def initialize_tracking(self, slots, frame_id):
        """Initialize or update slot tracking"""
        for slot in slots:
            slot_id = f"{slot['class']}_{hashlib.md5(str(slot['bbox']).encode()).hexdigest()[:8]}"
            
            if slot_id not in self.tracked_slots:
                self.tracked_slots[slot_id] = {
                    'class': slot['class'],
                    'positions': deque(maxlen=30),
                    'last_seen': frame_id,
                    'stability_score': 0.0
                }
            
            center = self.get_center(slot['bbox'])
            self.tracked_slots[slot_id]['positions'].append(center)
            self.tracked_slots[slot_id]['last_seen'] = frame_id
    
    def calculate_temporal_score(self, weapon_class, slot_class, frame_id):
        """Calculate score based on historical assignments"""
        history = self.mapping_history[weapon_class]
        
        if not history:
            return 0.5
        
        # Count recent assignments to this slot
        recent_frames = list(history)[-5:]  # Last 5 frames
        slot_assignments = sum(1 for assignment in recent_frames 
                             if assignment.get('slot') == slot_class)
        
        return min(1.0, slot_assignments / len(recent_frames))
    
    # 5️⃣ Confidence Logging & Analysis
        # 5️⃣ Confidence Logging & Analysis
    def log_mapping_attempt(self, weapon, slot, score_data, success=True):
        """Log detailed mapping attempt for analysis - FIXED for JSON serialization"""
        # Convert numpy types to Python native types
        def convert_numpy(obj):
            if isinstance(obj, np.generic):
                return obj.item()
            elif isinstance(obj, dict):
                return {k: convert_numpy(v) for k, v in obj.items()}
            elif isinstance(obj, list):
                return [convert_numpy(item) for item in obj]
            else:
                return obj
        
        # Convert score_data
        score_data_serializable = convert_numpy(score_data)
        
        log_entry = {
            'timestamp': datetime.now().isoformat(),
            'weapon': weapon['class'],
            'slot': slot if slot else 'none',
            'weapon_confidence': float(weapon['confidence']) if isinstance(weapon['confidence'], np.generic) else weapon['confidence'],
            'mapping_score': score_data_serializable.get('score', 0),
            'distance': score_data_serializable.get('distance', 0),
            'normalized_distance': score_data_serializable.get('normalized_distance', 0),
            'iou': score_data_serializable.get('factors', {}).get('iou', 0),
            'success': success,
            'detailed_factors': score_data_serializable.get('factors', {})
        }
        
        self.distance_log.append(log_entry)
        
        # Update performance stats with Python native types
        self.performance_stats['total_mappings'] += 1
        if success:
            self.performance_stats['successful_mappings'] += 1
            if slot:
                self.performance_stats['slot_hit_rates'][slot]['hits'] += 1
        else:
            self.performance_stats['failed_mappings'] += 1
            if slot:
                self.performance_stats['slot_hit_rates'][slot]['misses'] += 1
        
        norm_dist = score_data_serializable.get('normalized_distance', 0)
        confidence_val = score_data_serializable.get('factors', {}).get('confidence', 0)
        
        self.performance_stats['distance_distribution'].append(float(norm_dist))
        self.performance_stats['confidence_distribution'].append(float(confidence_val))
    
    # 🔍 NEW: Log scope mappings
    def log_scope_mapping(self, scope, weapon, slot, score_data, success=True):
        """Log scope mapping attempts"""
        log_entry = {
            'timestamp': datetime.now().isoformat(),
            'type': 'scope_mapping',
            'scope': scope['class'],
            'weapon': weapon if weapon else 'none',
            'slot': slot if slot else 'none',
            'scope_confidence': scope['confidence'],
            'mapping_score': score_data.get('score', 0),
            'distance': score_data.get('distance', 0),
            'success': success
        }
        
        self.distance_log.append(log_entry)
    
    # 6️⃣ IoU Filtering
    def calculate_iou(self, box1, box2):
        """Calculate Intersection over Union"""
        x1 = max(box1[0], box2[0])
        y1 = max(box1[1], box2[1])
        x2 = min(box1[2], box2[2])
        y2 = min(box1[3], box2[3])
        
        if x2 < x1 or y2 < y1:
            return 0.0
        
        intersection = (x2 - x1) * (y2 - y1)
        area1 = (box1[2] - box1[0]) * (box1[3] - box1[1])
        area2 = (box2[2] - box2[0]) * (box2[3] - box2[1])
        union = area1 + area2 - intersection
        
        return intersection / union if union > 0 else 0.0
    
    # 7️⃣ Distance Normalization
    def normalize_distance(self, distance, image_shape, method='diagonal'):
        """Normalize distance based on image size"""
        h, w = image_shape[:2]
        
        if method == 'diagonal':
            max_dist = np.sqrt(h**2 + w**2)
        elif method == 'width':
            max_dist = w
        elif method == 'height':
            max_dist = h
        else:
            max_dist = max(w, h)
        
        return distance / max_dist if max_dist > 0 else 0
    
    # 8️⃣ Multi-Pass Detection Integration
    def merge_detections(self, detection_sets):
        """Merge detections from multiple confidence passes"""
        merged = []
        seen_boxes = set()
        
        for detection_set in detection_sets:
            for det in detection_set:
                box_key = tuple(np.round(det['bbox']).astype(int))
                
                if box_key not in seen_boxes:
                    # Check if this box overlaps significantly with existing
                    is_duplicate = False
                    for existing in merged:
                        iou = self.calculate_iou(det['bbox'], existing['bbox'])
                        if iou > 0.5:  # 50% overlap threshold
                            is_duplicate = True
                            # Keep higher confidence
                            if det['confidence'] > existing['confidence']:
                                existing.update(det)
                            break
                    
                    if not is_duplicate:
                        merged.append(det)
                        seen_boxes.add(box_key)
        
        return merged
    
    # Utility methods
    def get_center(self, bbox):
        return ((bbox[0] + bbox[2]) / 2, (bbox[1] + bbox[3]) / 2)
    
    def calculate_distance(self, point1, point2):
        return np.sqrt((point1[0] - point2[0])**2 + (point1[1] - point2[1])**2)
    
    def calculate_area(self, bbox):
        return (bbox[2] - bbox[0]) * (bbox[3] - bbox[1])
    
    # 9️⃣ Reporting and Analysis
    def generate_performance_report(self):
        """Generate detailed performance analysis"""
        total_mappings = max(self.performance_stats['total_mappings'], 1)
        scope_mappings = max(self.performance_stats['scope_mappings'], 1)
        
        report = {
            'summary': {
                'total_mappings': self.performance_stats['total_mappings'],
                'success_rate': self.performance_stats['successful_mappings'] / total_mappings,
                'scope_mappings': self.performance_stats['scope_mappings'],
                'scope_success_rate': self.performance_stats['scope_success'] / scope_mappings,
                'average_distance': np.mean(self.performance_stats['distance_distribution']) 
                if self.performance_stats['distance_distribution'] else 0,
                'average_confidence': np.mean(self.performance_stats['confidence_distribution']) 
                if self.performance_stats['confidence_distribution'] else 0
            },
            'slot_performance': {},
            'distance_analysis': {
                'mean': np.mean(self.performance_stats['distance_distribution']) 
                if self.performance_stats['distance_distribution'] else 0,
                'std': np.std(self.performance_stats['distance_distribution']) 
                if self.performance_stats['distance_distribution'] else 0,
                'min': min(self.performance_stats['distance_distribution']) 
                if self.performance_stats['distance_distribution'] else 0,
                'max': max(self.performance_stats['distance_distribution']) 
                if self.performance_stats['distance_distribution'] else 0
            }
        }
        
        # Calculate slot hit rates
        for slot, stats in self.performance_stats['slot_hit_rates'].items():
            total = stats['hits'] + stats['misses']
            if total > 0:
                report['slot_performance'][slot] = {
                    'hit_rate': stats['hits'] / total,
                    'total_attempts': total,
                    'hits': stats['hits'],
                    'misses': stats['misses']
                }
        
        return report
    
    def save_all_logs(self, prefix="mega_analysis"):
        """Save all logs and analysis data"""
        # Convert distance log to Python native types
        def convert_numpy(obj):
            if isinstance(obj, np.integer):
                return int(obj)
            elif isinstance(obj, np.floating):
                return float(obj)
            elif isinstance(obj, np.ndarray):
                return obj.tolist()
            elif isinstance(obj, dict):
                return {k: convert_numpy(v) for k, v in obj.items()}
            elif isinstance(obj, list):
                return [convert_numpy(item) for item in obj]
            else:
                return obj
        
        python_distance_log = convert_numpy(self.distance_log)
        
        # Save distance log
        with open(f"{prefix}_distance_log.json", 'w') as f:
            json.dump(python_distance_log, f, indent=2)
        
        # Save performance report
        report = convert_numpy(self.generate_performance_report())
        with open(f"{prefix}_performance_report.json", 'w') as f:
            json.dump(report, f, indent=2)
        
        # Save CSV for easy analysis
        if python_distance_log:
            df = pd.DataFrame(python_distance_log)
            df.to_csv(f"{prefix}_mapping_data.csv", index=False)
        
        print(f"📊 All logs saved with prefix: {prefix}")
        
        return {
            'distance_log': f"{prefix}_distance_log.json",
            'performance_report': f"{prefix}_performance_report.json",
            'mapping_data': f"{prefix}_mapping_data.csv"
        }

class MEGAWeaponSlotMapper:
    """MEGA-PRO mapper with all 10 improvements + scope mapping"""
    
    def __init__(self, enable_temporal=True):
        self.tracker = MEGASlotTracker()
        self.enable_temporal = enable_temporal
        self.frame_counter = 0
        
    def mega_mapping_pipeline(self, weapons, slots, scopes, image_shape, filename):
        """Complete mapping pipeline with all enhancements including scopes"""
        self.frame_counter += 1
        
        # Initialize tracking if enabled
        if self.enable_temporal:
            self.tracker.initialize_tracking(slots, self.frame_counter)
        
        # Define enhanced slot regions with IoU
        slot_regions = self.tracker.define_slot_regions_with_iou(slots, image_shape)
        self.tracker.slot_regions[filename] = slot_regions
        
        # Step 1: Map weapons to slots
        weapon_slot_mapping = {}
        used_slots = set()
        mapping_details = {}
        
        # Sort weapons by confidence and size (larger first)
        weapons_sorted = sorted(
            weapons, 
            key=lambda w: (w['confidence'], self.tracker.calculate_area(w['bbox'])), 
            reverse=True
        )
        
        for weapon in weapons_sorted:
            # Get available slots (not used yet)
            available_slots = [s for s in slots if s['class'] not in used_slots]
            
            # Run MEGA weighted mapping
            best_slot, best_score, score_data = self.tracker.weighted_slot_mapping_mega(
                weapon, available_slots, image_shape, 
                self.frame_counter if self.enable_temporal else None
            )
            
            if best_slot and best_slot not in used_slots:
                weapon_slot_mapping[weapon['class']] = best_slot
                used_slots.add(best_slot)
                mapping_details[weapon['class']] = score_data
                
                # Log successful mapping
                self.tracker.log_mapping_attempt(weapon, best_slot, score_data, success=True)
                
                # Update history for temporal tracking
                if self.enable_temporal:
                    self.tracker.mapping_history[weapon['class']].append({
                        'frame': self.frame_counter,
                        'slot': best_slot,
                        'score': best_score,
                        'position': self.tracker.get_center(weapon['bbox'])
                    })
            else:
                # Fallback strategies
                assigned_slot = self.apply_fallback_strategies(
                    weapon, slots, used_slots, slot_regions, image_shape
                )
                
                if assigned_slot:
                    weapon_slot_mapping[weapon['class']] = assigned_slot
                    used_slots.add(assigned_slot)
                    mapping_details[weapon['class']] = {'score': 0.2, 'factors': {'fallback': True}}
                    self.tracker.log_mapping_attempt(weapon, assigned_slot, {}, success=True)
                else:
                    weapon_slot_mapping[weapon['class']] = "No slot"
                    self.tracker.log_mapping_attempt(weapon, None, {}, success=False)
        
        # Step 2: Map scopes to weapons and then to slots
        scope_weapon_mapping, scope_slot_mapping = self.tracker.map_scopes_to_weapons_with_distance_fallback(
            scopes, weapons, image_shape, weapon_slot_mapping
        )
        
        # Log scope mappings
        for scope_name, mapping_info in scope_weapon_mapping.items():
            scope_obj = next((s for s in scopes if s['class'] == scope_name), None)
            if scope_obj:
                slot = scope_slot_mapping.get(scope_name, "No slot")
                self.tracker.log_scope_mapping(
                    scope_obj, 
                    mapping_info['weapon'], 
                    slot,
                    {'score': mapping_info['score'], 'distance': mapping_info['distance']},
                    success=(slot != "No slot")
                )
        
        # Store positions for visualization
        self.tracker.weapon_positions[filename] = [
            {'class': w['class'], 'center': self.tracker.get_center(w['bbox'])}
            for w in weapons
        ]
        
        self.tracker.scope_positions[filename] = [
            {'class': s['class'], 'center': self.tracker.get_center(s['bbox'])}
            for s in scopes
        ]
        
        return weapon_slot_mapping, scope_slot_mapping, scope_weapon_mapping, mapping_details, slot_regions
    
    def apply_fallback_strategies(self, weapon, slots, used_slots, slot_regions, image_shape):
        """Apply multiple fallback strategies"""
        weapon_center = self.tracker.get_center(weapon['bbox'])
        
        # Strategy 1: Region containment
        for slot in slots:
            if slot['class'] not in used_slots:
                region = slot_regions.get(slot['class'], {})
                if 'expanded' in region:
                    if self.is_weapon_in_slot_region(weapon_center, region):
                        return slot['class']
        
        # Strategy 2: Nearest slot with distance threshold
        nearest_slot = None
        min_distance = float('inf')
        
        for slot in slots:
            if slot['class'] not in used_slots:
                slot_center = self.tracker.get_center(slot['bbox'])
                dist = self.tracker.calculate_distance(weapon_center, slot_center)
                
                if dist < min_distance:
                    min_distance = dist
                    nearest_slot = slot['class']
        
        # Check if within threshold
        if nearest_slot and min_distance < image_shape[1] * self.tracker.config['distance_threshold']:
            return nearest_slot
        
        # Strategy 3: Grid-based assignment (PUBG specific)
        return self.grid_based_fallback(weapon_center, image_shape, used_slots)
    
    def grid_based_fallback(self, weapon_center, image_shape, used_slots):
        """Grid-based fallback for PUBG inventory"""
        h, w = image_shape[:2]
        x, y = weapon_center
        
        # PUBG inventory typically has 2-3 vertical slots
        if y < h * 0.4 and 'slot_1' not in used_slots:
            return 'slot_1'
        elif y < h * 0.7 and 'slot_2' not in used_slots:
            return 'slot_2'
        #elif 'slot_3' not in used_slots:
        #    return 'slot_3'
        
        return None
    
    def is_weapon_in_slot_region(self, weapon_center, slot_region):
        """Check if weapon center falls inside slot's expanded region"""
        if 'expanded' not in slot_region:
            return False
        x, y = weapon_center
        sx1, sy1, sx2, sy2 = slot_region['expanded']
        return sx1 <= x <= sx2 and sy1 <= y <= sy2
    
    # Enhanced visualization with scopes
    def create_mega_visualization(self, img, weapons, slots, scopes, 
                                 weapon_mapping, scope_mapping, scope_weapon_mapping, 
                                 mapping_details, slot_regions):
        """Create visualization with ALL debug information including scopes"""
        debug_img = img.copy()
        h, w = img.shape[:2]
        
        # Add distance debug for scopes
        for scope_name, mapping_info in scope_weapon_mapping.items():
            scope = next((s for s in scopes if s['class'] == scope_name), None)
            weapon = next((w for w in weapons if w['class'] == mapping_info['weapon']), None)
            if scope and weapon:
                self.tracker.add_scope_distance_debug(debug_img, scope, weapon, mapping_info)
        
        # Draw enhanced slot regions with IoU info
        for slot_name, region in slot_regions.items():
            # Expanded region
            ex1, ey1, ex2, ey2 = map(int, region['expanded'])
            cv2.rectangle(debug_img, (ex1, ey1), (ex2, ey2), (100, 100, 255), 1)
            
            # Original slot
            x1, y1, x2, y2 = map(int, region['original'])
            cv2.rectangle(debug_img, (x1, y1), (x2, y2), (255, 165, 0), 2)
            
            # Slot info
            cv2.putText(debug_img, f"{slot_name} ({region['confidence']:.0%})", 
                       (x1, y1 - 10), cv2.FONT_HERSHEY_SIMPLEX, 0.5, (255, 165, 0), 2)
        
        # Draw weapons with detailed info
        for weapon in weapons:
            x1, y1, x2, y2 = map(int, weapon['bbox'])
            
            # Weapon box
            cv2.rectangle(debug_img, (x1, y1), (x2, y2), (0, 255, 0), 2)
            
            # Weapon info
            info_y = y1 - 30
            cv2.putText(debug_img, weapon['class'], (x1, info_y), 
                       cv2.FONT_HERSHEY_SIMPLEX, 0.6, (0, 255, 0), 2)
            cv2.putText(debug_img, f"{weapon['confidence']:.1%}", 
                       (x1, info_y + 20), cv2.FONT_HERSHEY_SIMPLEX, 0.5, (0, 255, 0), 1)
        
        # Draw scopes with blue color
        for scope in scopes:
            x1, y1, x2, y2 = map(int, scope['bbox'])
            
            # Scope box (blue)
            cv2.rectangle(debug_img, (x1, y1), (x2, y2), (255, 0, 0), 2)
            
            # Scope info
            info_y = y1 - 30
            cv2.putText(debug_img, scope['class'], (x1, info_y), 
                       cv2.FONT_HERSHEY_SIMPLEX, 0.6, (255, 0, 0), 2)
            cv2.putText(debug_img, f"{scope['confidence']:.1%}", 
                       (x1, info_y + 20), cv2.FONT_HERSHEY_SIMPLEX, 0.5, (255, 0, 0), 1)
        
        # Draw weapon-to-slot mapping connections
        for weapon_name, slot_name in weapon_mapping.items():
            if slot_name != "No slot":
                weapon = next((w for w in weapons if w['class'] == weapon_name), None)
                region = slot_regions.get(slot_name)
                
                if weapon and region:
                    w_center = self.tracker.get_center(weapon['bbox'])
                    s_center = region['center']
                    
                    # Draw connection
                    w_center_int = tuple(map(int, w_center))
                    s_center_int = tuple(map(int, s_center))
                    
                    # Color based on mapping quality
                    details = mapping_details.get(weapon_name, {})
                    score = details.get('score', 0)
                    
                    if score > 0.6:
                        color = (0, 255, 0)  # Green = excellent
                        thickness = 3
                    elif score > 0.4:
                        color = (255, 255, 0)  # Yellow = good
                        thickness = 2
                    else:
                        color = (255, 165, 0)  # Orange = poor
                        thickness = 1
                    
                    cv2.line(debug_img, w_center_int, s_center_int, color, thickness)
                    
                    # Draw score bubble
                    mid_x = (w_center_int[0] + s_center_int[0]) // 2
                    mid_y = (w_center_int[1] + s_center_int[1]) // 2
                    
                    cv2.circle(debug_img, (mid_x, mid_y), 20, color, -1)
                    cv2.putText(debug_img, f"{score:.2f}", (mid_x-15, mid_y+5),
                               cv2.FONT_HERSHEY_SIMPLEX, 0.5, (0, 0, 0), 2)
        
        # Draw scope-to-weapon mapping connections (blue dashed lines)
        for scope_name, mapping_info in scope_weapon_mapping.items():
            scope = next((s for s in scopes if s['class'] == scope_name), None)
            weapon = next((w for w in weapons if w['class'] == mapping_info['weapon']), None)
            
            if scope and weapon:
                s_center = self.tracker.get_center(scope['bbox'])
                w_center = self.tracker.get_center(weapon['bbox'])
                
                s_center_int = tuple(map(int, s_center))
                w_center_int = tuple(map(int, w_center))
                
                # Draw dashed blue line for scope-weapon connection
                self.draw_dashed_line(debug_img, s_center_int, w_center_int, 
                                     (255, 0, 0), 2, dash_length=10)
                
                # Draw small blue circle at scope end
                cv2.circle(debug_img, s_center_int, 8, (255, 0, 0), -1)
                
                # Draw scope mapping score
                mid_x = (s_center_int[0] + w_center_int[0]) // 2
                mid_y = (s_center_int[1] + w_center_int[1]) // 2
                
                score = mapping_info['score']
                cv2.putText(debug_img, f"Scope: {score:.2f}", 
                           (mid_x, mid_y - 10), cv2.FONT_HERSHEY_SIMPLEX, 
                           0.5, (255, 0, 0), 2)
        
        # Add heatmap overlay for distance distribution
        self.add_distance_heatmap(debug_img)
        
        # Add comprehensive legend with scope info
        self.add_mega_legend(debug_img)
        
        # Add performance stats
        self.add_performance_overlay(debug_img)
        
        return debug_img
    
    def draw_dashed_line(self, img, pt1, pt2, color, thickness=1, dash_length=10):
        """Draw dashed line between two points"""
        dist = np.sqrt((pt2[0] - pt1[0])**2 + (pt2[1] - pt1[1])**2)
        dashes = int(dist / dash_length)
        
        for i in range(dashes):
            start = i / dashes
            end = (i + 0.5) / dashes  # 50% dash, 50% gap
            
            start_pt = (int(pt1[0] + (pt2[0] - pt1[0]) * start),
                       int(pt1[1] + (pt2[1] - pt1[1]) * start))
            end_pt = (int(pt1[0] + (pt2[0] - pt1[0]) * end),
                     int(pt1[1] + (pt2[1] - pt1[1]) * end))
            
            cv2.line(img, start_pt, end_pt, color, thickness)
    
    def add_distance_heatmap(self, img):
        """Add heatmap visualization of distances"""
        h, w = img.shape[:2]
        
        # Create gradient for distance reference
        for x in range(0, w, 10):
            normalized_x = x / w
            color_intensity = int(255 * (1 - normalized_x))
            cv2.line(img, (x, h-50), (x, h-30), 
                    (0, 0, color_intensity), 10)
        
        cv2.putText(img, "Distance Heatmap (closer = brighter)", 
                   (10, h-55), cv2.FONT_HERSHEY_SIMPLEX, 0.4, (255, 255, 255), 1)
    
    def add_mega_legend(self, img):
        """Add comprehensive legend with scope info"""
        h, w = img.shape[:2]
        
        legend_items = [
            ("Excellent (>.60)", (0, 255, 0), "score > 0.6"),
            ("Good (.40-.60)", (255, 255, 0), "score 0.4-0.6"),
            ("Poor (<.40)", (255, 165, 0), "score < 0.4"),
            ("Weapon Box", (0, 255, 0), "detected weapon"),
            ("Scope Box", (255, 0, 0), "detected scope"),
            ("Slot Box", (255, 165, 0), "detected slot"),
            ("Expanded Region", (100, 100, 255), "search area"),
            ("Scope → Weapon", (255, 0, 0), "dashed blue line"),
            ("Weapon → Slot", (0, 255, 255), "solid colored line"),
        ]
        
        y_start = h - 250
        for i, (text, color, desc) in enumerate(legend_items):
            y = y_start + i * 25
            cv2.rectangle(img, (10, y-12), (25, y+3), color, -1)
            cv2.putText(img, text, (30, y), 
                       cv2.FONT_HERSHEY_SIMPLEX, 0.4, (255, 255, 255), 1)
            cv2.putText(img, desc, (150, y), 
                       cv2.FONT_HERSHEY_SIMPLEX, 0.4, (150, 150, 150), 1)
    
    def add_performance_overlay(self, img):
        """Add real-time performance stats overlay"""
        report = self.tracker.generate_performance_report()
        
        stats_text = [
            f"Weapon Success: {report['summary']['success_rate']:.1%}",
            f"Scope Success: {report['summary']['scope_success_rate']:.1%}",
            f"Avg Distance: {report['distance_analysis']['mean']:.3f}",
            f"Total Mappings: {report['summary']['total_mappings']}",
            f"Scope Mappings: {report['summary']['scope_mappings']}",
        ]
        
        y_offset = 30
        for text in stats_text:
            cv2.putText(img, text, (img.shape[1] - 250, y_offset),
                       cv2.FONT_HERSHEY_SIMPLEX, 0.5, (255, 255, 255), 1)
            y_offset += 25

# ============================================================================
# COMBINED REAL-TIME DETECTOR WITH MEGA MAPPING
# ============================================================================

def categorize_detection(class_name):
    """Comprehensive categorization for PUBG items"""
    class_lower = class_name.lower().replace('_', ' ').replace('-', ' ')
    
    # Check for slots first
    if 'slot' in class_lower:
        return 'slot'
    
    # Comprehensive scope/optic list
    scope_keywords = [
        'red', 'holo', '2x', '3x', '4x', '6x', '8x', '15x',
        'x2', 'x3', 'x4', 'x6', 'x8', 'x15', 
        'scope', 'optic', 'sight', 'acog', 'canted',
        'red dot', 'holo sight', 'red dot sight', 'holo scope',
        '2 times', '3 times', '4 times', '6 times', '8 times',
        'vss', 'pso-1', 'pso1', 'pu scope', 'pu sight'
    ]
    
    if any(keyword in class_lower for keyword in scope_keywords):
        return 'scope'
    
    # Comprehensive weapon list
    weapon_keywords = [
        # Assault Rifles
        'akm', 'm416', 'm4', 'scar-l', 'scar', 'beryl', 'ace32', 'ace 32', 'ace',
        'groza', 'aug a3', 'aug', 'mk47', 'mutant', 'mk14', 
        'm16a4', 'm16', 'qbz', 'g36c',
        
        # SMGs
        'ump', 'vector', 'uzi', 'mp5k', 'mp5', 'thompson', 'tommy',
        'bizon', 'pp-19', 'pp19',
        
        # DMRs
        'sks', 'slr', 'mini14', 'mini 14', 'qbu', 'mk12',
        
        # Snipers
        'kar98', 'kar98k', 'kar 98', 'm24', 'awm', 'mosin', 'win94', 'winchester',
        
        # LMGs
        'dp28', 'dp-28', 'dp 28', 'm249', 'mg3',
        
        # Shotguns
        's686', 's1897', 's12k', 'dbs', 'sawed-off', 'sawed off',
        
        # Pistols
        'p92', 'p1911', 'p18c', 'r1895', 'r45', 'deagle', 'skorpion',
        
        # Others
        'crossbow', 'pan', 'machete', 'crowbar', 'sickle',
        
        # Specific variants
        'dp28', 'dp-28', 'dp_28', 'mutant', 'mk47 mutant',
        '8x scope', '15x scope'
    ]
    
    if any(keyword in class_lower for keyword in weapon_keywords):
        return 'weapon'
    
    # Attachment/accessory detection
    attachment_keywords = [
        'extended', 'suppressor', 'compensator', 'flash', 'muzzle',
        'mag', 'magazine', 'quickdraw', 'grip', 'foregrip', 'angled',
        'vertical', 'half', 'thumb', 'laser', 'tactical', 'stock',
        'cheek', 'bullet', 'loop', 'quiver', 'choke', 'duckbill',
        'lightweight', 'ergonomic', 'laser sight'
    ]
    
    if any(keyword in class_lower for keyword in attachment_keywords):
        return 'attachment'
    
    print(f"⚠️ Unknown class detected: {class_name} (categorized as 'unknown')")
    return 'unknown'

def img_to_base64(img):
    """Convert image to base64"""
    img_rgb = cv2.cvtColor(img, cv2.COLOR_BGR2RGB)
    pil_img = Image.fromarray(img_rgb)
    buffered = BytesIO()
    pil_img.save(buffered, format="PNG")
    return base64.b64encode(buffered.getvalue()).decode()

def enhanced_detection(model, img, conf_levels=[0.1, 0.2, 0.25, 0.3, 0.35]):
    """Multi-pass detection with different confidence levels"""
    all_detections = []
    
    for conf in conf_levels:
        results = model(img, conf=conf, verbose=False)
        if results[0].boxes is not None:
            for box in results[0].boxes:
                detection = {
                    'class': model.names[int(box.cls[0])],
                    'confidence': float(box.conf[0]),
                    'bbox': box.xyxy[0].cpu().numpy(),
                    'type': categorize_detection(model.names[int(box.cls[0])])
                }
                all_detections.append(detection)
    
    # Merge and deduplicate
    tracker = MEGASlotTracker()
    merged = tracker.merge_detections([all_detections])
    return merged

class MEGAPUBGRealtimeDetector:
    """COMBINED: Real-time detector with MEGA mapping capabilities"""
    
    def __init__(self, model_path="best.pt"):
        print("🎮 MEGA PUBG REAL-TIME DETECTOR WITH SCOPE MAPPING")
        print("=" * 60)
        print("🔧 Features: Real-time + Advanced Mapping + Scope Detection")
        print("=" * 60)
        
        # Load model
        print("🤖 Loading model...")
        self.model = YOLO(model_path)
        self.model_names = self.model.names
        print(f"✅ Model loaded with {len(self.model_names)} classes")
        # Tab key detection 
        self.tab_pressed = False
        self.TAB_KEY = 0x09 # VK_TAB
        # Communication settings 
        self.zero_recoil_host = '127.0.0.1'
        self.zero_recoil_port = 7777
        self.zerp_recoil_connected = False
        self.communication_enabled =True
        self.last_sent_data = None # Avoid duplicates
        self.communication_thread = threading.Thread(target=self.communication_loop, daemon=True)
        self.communication_thread.start()

        print("✅ Zero Recoil communication system initialized")
        self.mapper = MEGAWeaponSlotMapper(enable_temporal=True)
        self.tracker = self.mapper.tracker
        
        # Screenshot capture
        self.sct = mss.mss()
        
        # Settings
        self.running = False
        self.confidence = 0.15
        self.enable_mega_mapping = True  # Enable advanced mapping
        
        # Inventory area - Default for 1920x1080
        self.monitor = {
            "top": 100,
            "left": 1300,
            "width": 400,
            "height": 600
        }
        
        # Results storage
        self.latest_image = None
        self.latest_detections = []
        self.latest_result = None
        self.latest_mappings = {
            'weapon_slot': {},
            'scope_slot': {},
            'scope_weapon': {},
            'details': {}
        }
        
        # Performance
        self.fps = 0
        self.detection_count = 0
        self.frame_counter = 0
        
        # Setup web server
        self.app = Flask(__name__)
        self.setup_routes()
        
        # Create output folder
        os.makedirs("captures", exist_ok=True)
        os.makedirs("mega_debug", exist_ok=True)
        
        print("✅ MEGA mapping engine initialized")
    def communication_loop(self):
        """Main communication loop with zero recoil system"""
        while True:
            try:
                # Check if TAB is pressed (inventory open)
                tab_state = win32api.GetAsyncKeyState(self.TAB_KEY) < 0
                self.tab_pressed = tab_state

                if self.tab_pressed and self.latest_mappings and self.communication_enabled:
                    self.send_to_zero_recoil()

                time.sleep(0.1)  # Check every 100ms
            except Exception as e:
                print(f">>> Communication loop error: {e}")
                time.sleep(1)
    def send_to_zero_recoil(self):
        """Send current inventory to zero recoil system"""
        if not self.communication_enabled or not self.latest_mappings:
            print(">>> Communication disabled or no mappings")
            return
    
        try:
            # Create socket
            client_socket = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            client_socket.settimeout(1.0)
    
            # Prepare mapping data - USE THE CORRECT KEYS
            weapon_mapping = self.latest_mappings.get('weapon_slot', {})
            scope_mapping = self.latest_mappings.get('scope_slot', {})
            scope_weapon_mapping = self.latest_mappings.get('scope_weapon', {})
    
            # Debug print
            print(f">>> DEBUG - weapon_mapping keys: {list(weapon_mapping.keys())}")
            print(f">>> DEBUG - weapon_mapping values: {list(weapon_mapping.values())}")
    
            # Convert to simple format for zero recoil
            inventory_data = {
                'tab_pressed': True,
                'timestamp': time.time(),
                'slots': {}
            }
    
            # Map detected weapons to slots (slot1, slot2, slot3)
            slot_counter = 1
    
            for weapon_class, slot_name in weapon_mapping.items():
                print(f">>> Processing weapon: {weapon_class} -> {slot_name}")

                if slot_name != "No slot" and slot_counter <= 3:
                    slot_key = f'slot{slot_counter}'
    
                    # Find scope for this weapon
                    scope_for_weapon = None
                    for scope_name, mapping_info in scope_weapon_mapping.items():
                        if mapping_info.get('weapon') == weapon_class:
                            scope_for_weapon = scope_name
                            print(f">>> Found scope {scope_for_weapon} for weapon {weapon_class}")
                            break
                         
                    # Convert weapon names to match zero recoil system
                    weapon_type = weapon_class.upper()  # Just uppercase it
                    scope_type = self.classify_scope_type(scope_for_weapon) if scope_for_weapon else "IRON SIGHTS"
    
                    inventory_data['slots'][slot_key] = {
                        'weapon': weapon_type,
                        'scope': scope_type,
                        'original_detected_name': weapon_class,
                        'original_scope_name': scope_for_weapon,
                        'mapping_confidence': self.latest_mappings.get('details', {}).get(weapon_class, {}).get('score', 0.5)
                    }
    
                    slot_counter += 1
    
            print(f">>> Inventory data prepared: {inventory_data}")
    
            # Check if data has changed since last send
            if self.has_inventory_changed(inventory_data):
                try:
                    # Connect to zero recoil system
                    client_socket.connect((self.zero_recoil_host, self.zero_recoil_port))
    
                    # Send data
                    json_data = json.dumps(inventory_data)
                    client_socket.send(json_data.encode('utf-8'))
    
                    print(f">>> ✅ Sent inventory to zero recoil: {inventory_data['slots']}")
                    self.last_sent_data = inventory_data
                    self.zero_recoil_connected = True
    
                except ConnectionRefusedError:
                    print(">>> ❌ Zero recoil system not listening")
                    self.zero_recoil_connected = False
                finally:
                    client_socket.close()
            else:
                print(">>> No change in inventory, skipping send")
    
        except Exception as e:
            print(f">>> ❌ Error sending to zero recoil: {e}")
            import traceback
            traceback.print_exc()
            self.zero_recoil_connected = False
    def classify_weapon_type(self, weapon_name):
            # Map to specific categories
        weapon_name_lower = weapon_name.lower()
        mapping = {
            # Assault Rifles
            'm416': 'ASSAULT RIFLE',
            'akm': 'ASSAULT RIFLE',
            'beryl': 'ASSAULT RIFLE',
            'scar-l': 'ASSAULT RIFLE',
            'groza': 'ASSAULT RIFLE',
            'aug a3': 'ASSAULT RIFLE',
            'aug': 'ASSAULT RIFLE',
            'mk47 mutant': 'ASSAULT RIFLE',
            'mk47': 'ASSAULT RIFLE',
            'mutant': 'ASSAULT RIFLE',
            'g36c': 'ASSAULT RIFLE',
            'm16a4': 'ASSAULT RIFLE',
            'm16': 'ASSAULT RIFLE',
            'qbz': 'ASSAULT RIFLE',
            
            # SMGs
            'ump45': 'SMG',
            'ump': 'SMG',
            'vector': 'SMG',
            'uzi': 'SMG',
            'mp5k': 'SMG',
            'mp5': 'SMG',
            'thompson': 'SMG',
            'tommy': 'SMG',
            'bizon': 'SMG',
            'pp-19': 'SMG',
            'pp19': 'SMG',
            
            # LMGs
            'dp28': 'LMG',
            'dp-28': 'LMG',
            'm249': 'LMG',
            'mg3': 'LMG',
            
            # Snipers
            'kar98k': 'SNIPER',
            'kar98': 'SNIPER',
            'm24': 'SNIPER',
            'awm': 'SNIPER',
            'mosin': 'SNIPER',
            'winchester': 'SNIPER',
            'win94': 'SNIPER',
            
            # Shotguns
            's1897': 'SHOTGUN',
            's686': 'SHOTGUN',
            's12k': 'SHOTGUN',
            'dbs': 'SHOTGUN',
            
            # Pistols
            'p92': 'PISTOL',
            'p1911': 'PISTOL',
            'p18c': 'PISTOL',
            'r1895': 'PISTOL',
            'r45': 'PISTOL',
            'deagle': 'PISTOL',
            'desert eagle': 'PISTOL',
            'skorpion': 'PISTOL',
            
            # DMRs (map to SNIPER for zero recoil)
            'sks': 'SNIPER',
            'slr': 'SNIPER',
            'mini14': 'SNIPER',
            'mini 14': 'SNIPER',
            'qbu': 'SNIPER',
            'mk12': 'SNIPER',
            'vss': 'SNIPER'
        }
        
        # Try exact match first
        for key, value in mapping.items():
            if key == weapon_name_lower:
                return value, key.upper()
        
        # Try partial match
        for key, value in mapping.items():
            if key in weapon_name_lower:
                return value, key.upper()
        
        # Default
        return "ASSAULT RIFLE", weapon_name.upper()

    def classify_scope_type(self, scope_name):
        """Convert detected scope name to zero recoil scope type"""
        if not scope_name:
            return "IRON SIGHTS"

        scope_name_lower = scope_name.lower()

        if 'red' in scope_name_lower or 'dot' in scope_name_lower:
            return "RED DOT"
        elif 'holo' in scope_name_lower:
            return "HOLO"
        elif '2x' in scope_name_lower or 'x2' in scope_name_lower or 'acog' in scope_name_lower:
            return "x2 ACOG"
        elif '3x' in scope_name_lower or 'x3' in scope_name_lower:
            return "x3 SCOPE"
        elif '4x' in scope_name_lower or 'x4' in scope_name_lower:
            return "x4 SNIPER"
        elif '6x' in scope_name_lower or 'x6' in scope_name_lower:
            return "x6 LONG-RANGE"
        elif '8x' in scope_name_lower or 'x8' in scope_name_lower:
            return "x8 ELITE"
        elif '15x' in scope_name_lower or 'x15' in scope_name_lower:
            return "x12 TITAN"  # Fallback

        return "IRON SIGHTS"

    def has_inventory_changed(self, new_data):
        """Check if inventory has changed since last send"""
        if not self.last_sent_data:
            return True

        # Compare slots
        old_slots = self.last_sent_data.get('slots', {})
        new_slots = new_data.get('slots', {})

        if len(old_slots) != len(new_slots):
            return True

        for slot_name, slot_data in new_slots.items():
            if slot_name not in old_slots:
                return True

            old_slot = old_slots[slot_name]
            if (old_slot.get('weapon') != slot_data.get('weapon') or 
                old_slot.get('scope') != slot_data.get('scope')):
                return True

        return False
    def capture_screen(self):
        """Capture inventory area"""
        try:
            screenshot = self.sct.grab(self.monitor)
            img = np.array(screenshot)
            
            if img.shape[2] == 4:  # BGRA to BGR
                img = cv2.cvtColor(img, cv2.COLOR_BGRA2BGR)
            
            return img
        except Exception as e:
            print(f"❌ Capture error: {e}")
            return None
    
    def detect_with_mega_mapping(self, img):
        """Run detection with MEGA mapping - IMPROVED VERSION"""
        if img is None:
            return None, [], {}
        
        start_time = time.perf_counter()
        
        # Run enhanced detection
        detections = enhanced_detection(self.model, img, conf_levels=[self.confidence, self.confidence*1.5])
        
        # Debug: Print all detected classes
        print(f"\n📊 Detected {len(detections)} objects:")
        for det in detections:
            print(f"  • {det['class']} ({det['type']}): {det['confidence']:.1%}")
        
        # Categorize detections
        weapons = [d for d in detections if d['type'] == 'weapon']
        slots = [d for d in detections if d['type'] == 'slot']
        scopes = [d for d in detections if d['type'] == 'scope']
        
        # Apply MEGA mapping
        weapon_mapping = {}
        scope_mapping = {}
        scope_weapon_mapping = {}
        mapping_details = {}
        slot_regions = {}
        
        if self.enable_mega_mapping:
            weapon_mapping, scope_mapping, scope_weapon_mapping, mapping_details, slot_regions = \
                self.mapper.mega_mapping_pipeline(
                    weapons, slots, scopes, img.shape, f"frame_{self.frame_counter}"
                )
        
        # If MEGA mapping fails, try simpler mapping
        if not weapon_mapping and weapons and slots:
            print("⚠️  MEGA mapping failed, using simple distance-based mapping")
            weapon_mapping = self.simple_distance_mapping(weapons, slots, img.shape)
        
        # Create visualization
        result_img = img.copy()
        
        # Draw basic boxes with enhanced colors
        for det in detections:
            x1, y1, x2, y2 = map(int, det['bbox'])
            
            # Different colors for different types
            if det['type'] == 'weapon':
                color = (0, 255, 0)  # Green
            elif det['type'] == 'slot':
                color = (255, 165, 0)  # Orange
            elif det['type'] == 'scope':
                color = (255, 0, 0)  # Red
            elif det['type'] == 'attachment':
                color = (0, 255, 255)  # Cyan
            else:
                color = (255, 255, 255)  # White
            
            cv2.rectangle(result_img, (x1, y1), (x2, y2), color, 2)
            
            # Text label with confidence
            label = f"{det['class']} {det['confidence']:.0%}"
            cv2.putText(result_img, label, (x1, max(20, y1 - 10)), 
                       cv2.FONT_HERSHEY_SIMPLEX, 0.5, color, 2)
            
            # Draw detection type
            cv2.putText(result_img, det['type'], (x1, y2 + 20),
                       cv2.FONT_HERSHEY_SIMPLEX, 0.4, color, 1)
        
        # If MEGA mapping enabled, draw advanced visualization
        if self.enable_mega_mapping and (weapons or scopes or slots):
            try:
                result_img = self.mapper.create_mega_visualization(
                    result_img, weapons, slots, scopes,
                    weapon_mapping, scope_mapping, scope_weapon_mapping,
                    mapping_details, slot_regions
                )
            except Exception as e:
                print(f"⚠️  MEGA visualization failed: {e}")
                # Fallback to basic visualization
        
        # Draw simple connections if MEGA mapping is off
        elif not self.enable_mega_mapping:
            result_img = self.draw_simple_connections(result_img, weapons, slots, scopes)
        
        # Calculate FPS
        detection_time = (time.perf_counter() - start_time) * 1000
        self.fps = 1000 / max(1, detection_time)
        self.frame_counter += 1
        
        # Prepare detections for display
        display_detections = []
        for det in detections:
            display_detections.append({
                'class': det['class'],
                'confidence': float(det['confidence']) if hasattr(det['confidence'], 'item') else det['confidence'],
                'type': det['type']
            })
        
        # Store mappings
        self.latest_mappings = {
            'weapon_slot': weapon_mapping,
            'scope_slot': scope_mapping,
            'scope_weapon': scope_weapon_mapping,
            'details': mapping_details
        }
        
        return result_img, display_detections, {
            'weapons': weapons,
            'slots': slots,
            'scopes': scopes,
            'weapon_mapping': weapon_mapping,
            'scope_mapping': scope_mapping,
            'scope_weapon_mapping': scope_weapon_mapping
        }
    def draw_simple_connections(self, img, weapons, slots, scopes):
        """Draw simple connections between weapons, slots, and scopes"""
        h, w = img.shape[:2]
        
        # Connect weapons to nearest slots
        for weapon in weapons:
            w_center = self.mapper.tracker.get_center(weapon['bbox'])
            w_center_int = (int(w_center[0]), int(w_center[1]))
            
            # Find nearest slot
            nearest_slot = None
            min_distance = float('inf')
            
            for slot in slots:
                s_center = self.mapper.tracker.get_center(slot['bbox'])
                distance = self.mapper.tracker.calculate_distance(w_center, s_center)
                
                if distance < min_distance and distance < w * 0.4:  # Within 40% of width
                    min_distance = distance
                    nearest_slot = slot
            
            if nearest_slot:
                s_center = self.mapper.tracker.get_center(nearest_slot['bbox'])
                s_center_int = (int(s_center[0]), int(s_center[1]))
                
                # Draw connection line
                cv2.line(img, w_center_int, s_center_int, (0, 255, 255), 2)
                
                # Draw midpoint with weapon name
                mid_x = (w_center_int[0] + s_center_int[0]) // 2
                mid_y = (w_center_int[1] + s_center_int[1]) // 2
                
                cv2.putText(img, weapon['class'], (mid_x, mid_y),
                           cv2.FONT_HERSHEY_SIMPLEX, 0.5, (0, 255, 255), 2)
        
        # Connect scopes to nearest weapons
        for scope in scopes:
            s_center = self.mapper.tracker.get_center(scope['bbox'])
            s_center_int = (int(s_center[0]), int(s_center[1]))
            
            # Find nearest weapon (scope should be above weapon)
            nearest_weapon = None
            min_distance = float('inf')
            
            for weapon in weapons:
                w_center = self.mapper.tracker.get_center(weapon['bbox'])
                
                # Scope should be above weapon (positive dy)
                dy = w_center[1] - s_center[1]
                dx = abs(w_center[0] - s_center[0])
                
                if dy > 0 and dy < 100 and dx < 80:  # Scope above weapon, within range
                    distance = self.mapper.tracker.calculate_distance(s_center, w_center)
                    if distance < min_distance:
                        min_distance = distance
                        nearest_weapon = weapon
            
            if nearest_weapon:
                w_center = self.mapper.tracker.get_center(nearest_weapon['bbox'])
                w_center_int = (int(w_center[0]), int(w_center[1]))
                
                # Draw dashed line for scope connection
                self.mapper.draw_dashed_line(img, s_center_int, w_center_int, (255, 0, 0), 2, dash_length=10)
                
                # Label the scope
                cv2.putText(img, f"{scope['class']} -> {nearest_weapon['class']}", 
                           (s_center_int[0], s_center_int[1] - 20),
                           cv2.FONT_HERSHEY_SIMPLEX, 0.5, (255, 0, 0), 2)
        
        return img
    def simple_distance_mapping(self, weapons, slots, image_shape):
        """Simple distance-based mapping as fallback"""
        mapping = {}
        
        for weapon in weapons:
            w_center = self.mapper.tracker.get_center(weapon['bbox'])
            best_slot = None
            min_distance = float('inf')
            
            for slot in slots:
                s_center = self.mapper.tracker.get_center(slot['bbox'])
                distance = self.mapper.tracker.calculate_distance(w_center, s_center)
                
                # Normalize distance by image width
                normalized_distance = distance / image_shape[1]
                
                if normalized_distance < 0.4 and distance < min_distance:  # 40% threshold
                    min_distance = distance
                    best_slot = slot['class']
            
            if best_slot:
                mapping[weapon['class']] = best_slot
        
        return mapping
    
    def perform_single_detection(self):
        """Perform one detection cycle with MEGA mapping"""
        try:
            # Capture screen
            original = self.capture_screen()
            if original is None:
                return
            
            # Store original
            self.latest_image = original.copy()
            
            # Run detection with MEGA mapping
            result_img, detections, mapping_data = self.detect_with_mega_mapping(original)
            
            # Store results
            self.latest_result = result_img
            self.latest_detections = detections
            self.detection_count += 1
            
            # Save to file for debugging
            if detections:
                timestamp = int(time.time())
                cv2.imwrite(f"captures/detection_{timestamp}.png", result_img)
                cv2.imwrite(f"captures/original_{timestamp}.png", original)
                
                # Save MEGA debug image
                if mapping_data['weapons'] or mapping_data['scopes']:
                    cv2.imwrite(f"mega_debug/mega_{timestamp}.png", result_img)
            
            # Print to console
            if detections:
                print(f"\n🎯 Detected {len(detections)} objects:")
                for det in detections:
                    print(f"  • {det['type'].upper()}: {det['class']} ({det['confidence']:.1%})")
                
                # Print mappings
                if mapping_data['weapon_mapping']:
                    print("  🔫 Weapon-Slot Mappings:")
                    for weapon, slot in mapping_data['weapon_mapping'].items():
                        print(f"     ✅ {weapon} → {slot}")
                
                if mapping_data['scope_mapping']:
                    print("  🔭 Scope Mappings:")
                    for scope, slot in mapping_data['scope_mapping'].items():
                        weapon = mapping_data['scope_weapon_mapping'].get(scope, {}).get('weapon', 'Unknown')
                        print(f"     🔭 {scope} → {weapon} → {slot}")
                
                print(f"  📁 Saved to captures/detection_{timestamp}.png")
            else:
                print("❌ No detections")
            
        except Exception as e:
            print(f"❌ Detection error: {e}")
            import traceback
            traceback.print_exc()
    
    def run_detection_loop(self):
        """Main detection loop"""
        print("\n🎯 Starting MEGA detection loop...")
        print("Controls: F9=Toggle, F10=Force, F11=Toggle MEGA, ESC=Exit")
        
        last_print_time = time.time()
        
        while True:
            try:
                # Handle hotkeys
                if win32api.GetAsyncKeyState(0x78) < 0:  # F9
                    self.running = not self.running
                    status = "ACTIVE 🟢" if self.running else "PAUSED 🔴"
                    print(f"\n{'='*50}")
                    print(f"🎯 DETECTION {status}")
                    print(f"{'='*50}")
                    winsound.Beep(1000 if self.running else 500, 200)
                    time.sleep(0.3)
                
                if win32api.GetAsyncKeyState(0x79) < 0:  # F10
                    print("\n🎯 FORCING DETECTION...")
                    self.perform_single_detection()
                    time.sleep(0.3)
                
                if win32api.GetAsyncKeyState(0x7A) < 0:  # F11
                    self.enable_mega_mapping = not self.enable_mega_mapping
                    status = "ENABLED 🔥" if self.enable_mega_mapping else "DISABLED ⚪"
                    print(f"\n{'='*50}")
                    print(f"🔧 MEGA MAPPING {status}")
                    print(f"{'='*50}")
                    winsound.Beep(800, 200)
                    time.sleep(0.3)
                
                if win32api.GetAsyncKeyState(0x1B) < 0:  # ESC
                    print("\n🛑 Exiting...")
                    # Save logs before exiting
                    self.save_analysis_logs()
                    break
                
                # Run detection if active
                if self.running:
                    self.perform_single_detection()
                
                # Print status every 5 seconds
                if time.time() - last_print_time > 5:
                    mode = "MEGA 🔥" if self.enable_mega_mapping else "BASIC ⚪"
                    print(f"📊 Status: {'RUNNING' if self.running else 'PAUSED'} | Mode: {mode} | FPS: {self.fps:.1f} | Detections: {self.detection_count}")
                    last_print_time = time.time()
                
                # Don't spam detections too fast
                time.sleep(0.1 if self.running else 0.05)
                
            except KeyboardInterrupt:
                self.save_analysis_logs()
                break
            except Exception as e:
                print(f"❌ Error: {e}")
                time.sleep(1)
    
    def save_analysis_logs(self):
        """Save analysis logs before exit"""
        print("\n💾 Saving analysis logs...")
        try:
            log_files = self.tracker.save_all_logs(prefix=f"realtime_{int(time.time())}")
            print("✅ Logs saved successfully")
            return log_files
        except Exception as e:
            print(f"❌ Failed to save logs: {e}")
            return None
    
    def setup_routes(self):
        """Setup Flask web interface with MEGA features"""
        
        HTML = """
        <!DOCTYPE html>
        <html>
        <head>
            <title>🎮 PUBG MEGA Live Detection</title>
            <meta charset="utf-8">
            <style>
                body {
                    margin: 0;
                    padding: 20px;
                    background: #0f0f23;
                    color: white;
                    font-family: 'Segoe UI', Arial, sans-serif;
                }
                
                .container {
                    max-width: 1800px;
                    margin: 0 auto;
                }
                
                header {
                    text-align: center;
                    margin-bottom: 30px;
                    padding-bottom: 20px;
                    border-bottom: 2px solid #00ff00;
                    background: linear-gradient(90deg, #1a1a2e, #16213e);
                    border-radius: 15px;
                    padding: 25px;
                }
                
                h1 {
                    color: #00ff00;
                    font-size: 2.8em;
                    margin: 0;
                    text-shadow: 0 0 10px rgba(0,255,0,0.3);
                }
                
                .subtitle {
                    color: #00aaff;
                    margin-top: 10px;
                    font-size: 1.1em;
                }
                
                .dashboard {
                    display: grid;
                    grid-template-columns: 2fr 1fr;
                    gap: 25px;
                    margin-bottom: 30px;
                }
                
                @media (max-width: 1400px) {
                    .dashboard {
                        grid-template-columns: 1fr;
                    }
                }
                
                .image-section {
                    background: #1a1a2e;
                    border-radius: 15px;
                    padding: 25px;
                    border: 2px solid #444;
                    box-shadow: 0 10px 20px rgba(0,0,0,0.3);
                }
                
                .image-container {
                    display: grid;
                    grid-template-columns: 1fr 1fr;
                    gap: 20px;
                    margin-bottom: 25px;
                }
                
                .image-box {
                    text-align: center;
                }
                
                .image-box h3 {
                    color: #00aaff;
                    margin-bottom: 15px;
                    font-size: 1.3em;
                }
                
                .image-box img {
                    width: 100%;
                    max-width: 700px;
                    border: 2px solid #444;
                    border-radius: 10px;
                    background: black;
                    box-shadow: 0 5px 15px rgba(0,0,0,0.5);
                }
                
                .stats-section {
                    background: #1a1a2e;
                    border-radius: 15px;
                    padding: 25px;
                    border: 2px solid #444;
                    box-shadow: 0 10px 20px rgba(0,0,0,0.3);
                }
                
                .stat-grid {
                    display: grid;
                    grid-template-columns: 1fr 1fr;
                    gap: 20px;
                    margin-bottom: 25px;
                }
                
                .stat-card {
                    background: linear-gradient(135deg, #0a0a1a, #1a1a3a);
                    padding: 20px;
                    border-radius: 12px;
                    text-align: center;
                    border: 1px solid #00aaff;
                    transition: transform 0.3s;
                }
                
                .stat-card:hover {
                    transform: translateY(-5px);
                    box-shadow: 0 10px 20px rgba(0,170,255,0.2);
                }
                
                .stat-value {
                    font-size: 2.5em;
                    color: #00ff00;
                    font-weight: bold;
                    margin-bottom: 5px;
                }
                
                .stat-label {
                    color: #aaa;
                    font-size: 0.95em;
                }
                
                .mappings-section {
                    background: #1a1a2e;
                    border-radius: 15px;
                    padding: 25px;
                    border: 2px solid #444;
                    margin-bottom: 30px;
                    box-shadow: 0 10px 20px rgba(0,0,0,0.3);
                }
                
                .mapping-columns {
                    display: grid;
                    grid-template-columns: 1fr 1fr;
                    gap: 25px;
                    margin-top: 20px;
                }
                
                .mapping-column {
                    background: rgba(10,10,26,0.5);
                    padding: 20px;
                    border-radius: 10px;
                    border: 1px solid;
                }
                
                .weapon-mapping {
                    border-color: #00ff00;
                }
                
                .scope-mapping {
                    border-color: #ff0000;
                }
                
                .mapping-column h4 {
                    color: #00aaff;
                    margin-top: 0;
                    border-bottom: 1px solid;
                    padding-bottom: 10px;
                }
                
                .weapon-mapping h4 {
                    border-bottom-color: #00ff00;
                }
                
                .scope-mapping h4 {
                    border-bottom-color: #ff0000;
                }
                
                .mapping-item {
                    padding: 12px;
                    margin-bottom: 10px;
                    border-radius: 8px;
                    background: rgba(0,0,0,0.3);
                    border-left: 4px solid;
                    display: flex;
                    justify-content: space-between;
                    align-items: center;
                    transition: background 0.3s;
                }
                
                .mapping-item:hover {
                    background: rgba(0,0,0,0.5);
                }
                
                .weapon-item {
                    border-left-color: #00ff00;
                }
                
                .scope-item {
                    border-left-color: #ff0000;
                }
                
                .mapping-name {
                    font-weight: bold;
                    font-size: 1.1em;
                }
                
                .mapping-target {
                    color: #aaa;
                }
                
                .mapping-score {
                    background: #00ff00;
                    color: black;
                    padding: 4px 12px;
                    border-radius: 15px;
                    font-weight: bold;
                    font-size: 0.9em;
                }
                
                .scope-score {
                    background: #ff0000;
                    color: white;
                }
                
                .detections-section {
                    background: #1a1a2e;
                    border-radius: 15px;
                    padding: 25px;
                    border: 2px solid #444;
                    box-shadow: 0 10px 20px rgba(0,0,0,0.3);
                }
                
                .detection-item {
                    background: rgba(10,10,26,0.5);
                    padding: 12px;
                    margin-bottom: 10px;
                    border-radius: 8px;
                    border-left: 4px solid;
                    display: flex;
                    justify-content: space-between;
                    align-items: center;
                }
                
                .weapon-detection {
                    border-left-color: #00ff00;
                }
                
                .slot-detection {
                    border-left-color: #ffaa00;
                }
                
                .scope-detection {
                    border-left-color: #ff0000;
                }
                
                .detection-name {
                    font-weight: bold;
                    display: flex;
                    align-items: center;
                    gap: 10px;
                }
                
                .detection-icon {
                    font-size: 1.2em;
                }
                
                .detection-confidence {
                    background: #00aaff;
                    color: black;
                    padding: 4px 12px;
                    border-radius: 15px;
                    font-weight: bold;
                }
                
                .controls {
                    display: flex;
                    gap: 15px;
                    margin-top: 25px;
                    flex-wrap: wrap;
                }
                
                button {
                    padding: 12px 25px;
                    border: none;
                    border-radius: 10px;
                    font-weight: bold;
                    cursor: pointer;
                    transition: all 0.3s;
                    font-size: 1em;
                    display: flex;
                    align-items: center;
                    gap: 10px;
                }
                
                .btn-toggle {
                    background: linear-gradient(135deg, #00ff00, #00cc00);
                    color: black;
                }
                
                .btn-toggle:hover {
                    background: linear-gradient(135deg, #00cc00, #009900);
                    transform: translateY(-3px);
                    box-shadow: 0 5px 15px rgba(0,255,0,0.3);
                }
                
                .btn-detect {
                    background: linear-gradient(135deg, #00aaff, #0088cc);
                    color: white;
                }
                
                .btn-detect:hover {
                    background: linear-gradient(135deg, #0088cc, #006699);
                    transform: translateY(-3px);
                    box-shadow: 0 5px 15px rgba(0,170,255,0.3);
                }
                
                .btn-mega {
                    background: linear-gradient(135deg, #ff00ff, #cc00cc);
                    color: white;
                }
                
                .btn-mega:hover {
                    background: linear-gradient(135deg, #cc00cc, #990099);
                    transform: translateY(-3px);
                    box-shadow: 0 5px 15px rgba(255,0,255,0.3);
                }
                
                .status-indicator {
                    display: inline-block;
                    width: 12px;
                    height: 12px;
                    border-radius: 50%;
                    margin-right: 10px;
                }
                
                .status-active {
                    background: #00ff00;
                    box-shadow: 0 0 10px #00ff00;
                    animation: pulse 1.5s infinite;
                }
                
                .status-inactive {
                    background: #ff0000;
                }
                
                .status-mega {
                    background: #ff00ff;
                    box-shadow: 0 0 10px #ff00ff;
                }
                
                @keyframes pulse {
                    0% { opacity: 1; }
                    50% { opacity: 0.5; }
                    100% { opacity: 1; }
                }
                
                .calibration-box {
                    background: #1a1a2e;
                    border-radius: 15px;
                    padding: 25px;
                    border: 2px solid #ffaa00;
                    margin-bottom: 25px;
                    box-shadow: 0 10px 20px rgba(0,0,0,0.3);
                }
                
                .calibration-box h3 {
                    color: #ffaa00;
                    margin-top: 0;
                    font-size: 1.3em;
                }
                
                .calibration-input {
                    display: grid;
                    grid-template-columns: repeat(4, 1fr);
                    gap: 15px;
                    margin-bottom: 20px;
                }
                
                @media (max-width: 768px) {
                    .calibration-input {
                        grid-template-columns: 1fr 1fr;
                    }
                }
                
                .calibration-input div {
                    display: flex;
                    flex-direction: column;
                }
                
                .calibration-input label {
                    margin-bottom: 5px;
                    color: #ccc;
                }
                
                .calibration-input input {
                    padding: 10px;
                    border-radius: 8px;
                    border: 1px solid #444;
                    background: #0a0a1a;
                    color: white;
                    font-size: 1em;
                }
                
                footer {
                    text-align: center;
                    margin-top: 40px;
                    padding-top: 20px;
                    border-top: 1px solid #444;
                    color: #888;
                    font-size: 0.9em;
                }
                
                .features-badge {
                    display: inline-block;
                    background: linear-gradient(135deg, #ff00ff, #00aaff);
                    color: white;
                    padding: 5px 15px;
                    border-radius: 20px;
                    font-size: 0.8em;
                    margin-top: 10px;
                    font-weight: bold;
                }
                
                .empty-state {
                    text-align: center;
                    padding: 40px;
                    color: #888;
                    font-style: italic;
                }
            </style>
            <script>
                function updateDashboard() {
                    fetch('/api/status')
                        .then(response => response.json())
                        .then(data => {
                            // Update images
                            if (data.result_image) {
                                document.getElementById('resultImage').src = 'data:image/png;base64,' + data.result_image;
                            }
                            if (data.original_image) {
                                document.getElementById('originalImage').src = 'data:image/png;base64,' + data.original_image;
                            }
                            
                            // Update stats
                            document.getElementById('fps').textContent = data.fps.toFixed(1);
                            document.getElementById('detectionCount').textContent = data.detection_count;
                            document.getElementById('status').textContent = data.running ? 'ACTIVE' : 'PAUSED';
                            document.getElementById('statusIndicator').className = 
                                'status-indicator ' + (data.running ? 'status-active' : 'status-inactive');
                            document.getElementById('megaStatus').textContent = data.mega_enabled ? 'ENABLED 🔥' : 'DISABLED';
                            document.getElementById('megaIndicator').className = 
                                'status-indicator ' + (data.mega_enabled ? 'status-mega' : 'status-inactive');
                            
                            // Update weapon mappings
                            const weaponMappingsDiv = document.getElementById('weaponMappings');
                            weaponMappingsDiv.innerHTML = '';
                            
                            if (data.weapon_mappings && Object.keys(data.weapon_mappings).length > 0) {
                                for (const [weapon, slot] of Object.entries(data.weapon_mappings)) {
                                    if (slot !== "No slot") {
                                        const details = data.mapping_details[weapon] || {};
                                        const score = details.score || 0;
                                        const scoreColor = score > 0.6 ? '#00ff00' : score > 0.4 ? '#ffaa00' : '#ff5555';
                                        
                                        const div = document.createElement('div');
                                        div.className = 'mapping-item weapon-item';
                                        div.innerHTML = `
                                            <div>
                                                <div class="mapping-name">🔫 ${weapon}</div>
                                                <div class="mapping-target">→ ${slot}</div>
                                            </div>
                                            <span class="mapping-score" style="background: ${scoreColor}">${score.toFixed(2)}</span>
                                        `;
                                        weaponMappingsDiv.appendChild(div);
                                    }
                                }
                            } else {
                                weaponMappingsDiv.innerHTML = '<div class="empty-state">No weapon mappings yet</div>';
                            }
                            
                            // Update scope mappings
                            const scopeMappingsDiv = document.getElementById('scopeMappings');
                            scopeMappingsDiv.innerHTML = '';
                            
                            if (data.scope_mappings && Object.keys(data.scope_mappings).length > 0) {
                                for (const [scope, slot] of Object.entries(data.scope_mappings)) {
                                    if (slot !== "No slot") {
                                        const weaponInfo = data.scope_weapon_mappings[scope] || {};
                                        const weapon = weaponInfo.weapon || 'Unknown';
                                        const score = weaponInfo.score || 0;
                                        const scoreColor = score > 0.6 ? '#00ff00' : score > 0.4 ? '#ffaa00' : '#ff5555';
                                        
                                        const div = document.createElement('div');
                                        div.className = 'mapping-item scope-item';
                                        div.innerHTML = `
                                            <div>
                                                <div class="mapping-name">🔭 ${scope}</div>
                                                <div class="mapping-target">→ ${weapon} → ${slot}</div>
                                            </div>
                                            <span class="mapping-score scope-score" style="background: ${scoreColor}">${score.toFixed(2)}</span>
                                        `;
                                        scopeMappingsDiv.appendChild(div);
                                    }
                                }
                            } else {
                                scopeMappingsDiv.innerHTML = '<div class="empty-state">No scope mappings yet</div>';
                            }
                            
                            // Update detections
                            const detectionsDiv = document.getElementById('detections');
                            detectionsDiv.innerHTML = '';
                            
                            if (data.detections.length === 0) {
                                detectionsDiv.innerHTML = '<div class="empty-state">No detections yet</div>';
                            } else {
                                data.detections.forEach(det => {
                                    const icon = det.type === 'weapon' ? '🔫' : det.type === 'scope' ? '🔭' : '🔢';
                                    const typeClass = det.type + '-detection';
                                    
                                    const div = document.createElement('div');
                                    div.className = `detection-item ${typeClass}`;
                                    div.innerHTML = `
                                        <div class="detection-name">
                                            <span class="detection-icon">${icon}</span>
                                            ${det.class}
                                        </div>
                                        <span class="detection-confidence">${(det.confidence * 100).toFixed(0)}%</span>
                                    `;
                                    detectionsDiv.appendChild(div);
                                });
                            }
                            
                            // Update timestamp
                            document.getElementById('timestamp').textContent = new Date().toLocaleTimeString();
                        })
                        .catch(error => console.error('Error:', error));
                }
                
                function toggleDetection() {
                    fetch('/api/toggle', { method: 'POST' })
                        .then(response => response.json())
                        .then(data => {
                            updateDashboard();
                        });
                }
                
                function forceDetection() {
                    fetch('/api/force', { method: 'POST' })
                        .then(response => response.json())
                        .then(data => {
                            updateDashboard();
                        });
                }
                
                function toggleMega() {
                    fetch('/api/toggle_mega', { method: 'POST' })
                        .then(response => response.json())
                        .then(data => {
                            updateDashboard();
                        });
                }
                
                function updateCalibration() {
                    const top = document.getElementById('calTop').value;
                    const left = document.getElementById('calLeft').value;
                    const width = document.getElementById('calWidth').value;
                    const height = document.getElementById('calHeight').value;
                    
                    fetch('/api/calibrate', {
                        method: 'POST',
                        headers: {
                            'Content-Type': 'application/json',
                        },
                        body: JSON.stringify({ top, left, width, height })
                    })
                    .then(response => response.json())
                    .then(data => {
                        alert(data.message);
                        if (data.success) {
                            forceDetection();
                        }
                    });
                }
                
                function saveLogs() {
                    fetch('/api/save_logs', { method: 'POST' })
                        .then(response => response.json())
                        .then(data => {
                            alert(data.message);
                        });
                }
                
                // Auto-refresh every second
                setInterval(updateDashboard, 1000);
                
                // Initial load
                document.addEventListener('DOMContentLoaded', updateDashboard);
            </script>
        </head>
        <body>
            <div class="container">
                <header>
                    <h1>
                        <span id="statusIndicator" class="status-indicator status-active"></span>
                        🎮 PUBG MEGA LIVE DETECTION
                    </h1>
                    <div class="subtitle">
                        Real-time AI detection with Advanced Weapon & Scope Mapping | 
                        Last update: <span id="timestamp">--:--:--</span>
                    </div>
                    <div class="features-badge">🔥 MEGA MAPPING: <span id="megaStatus">ENABLED</span> <span id="megaIndicator" class="status-indicator status-mega"></span></div>
                </header>
                
                <div class="calibration-box">
                    <h3>⚙️ Calibration Settings</h3>
                    <p>Adjust these values if detection area is wrong:</p>
                    <div class="calibration-input">
                        <div>
                            <label>Top:</label>
                            <input type="number" id="calTop" value="100" min="0" max="2000">
                        </div>
                        <div>
                            <label>Left:</label>
                            <input type="number" id="calLeft" value="1300" min="0" max="3000">
                        </div>
                        <div>
                            <label>Width:</label>
                            <input type="number" id="calWidth" value="400" min="100" max="1000">
                        </div>
                        <div>
                            <label>Height:</label>
                            <input type="number" id="calHeight" value="600" min="100" max="1000">
                        </div>
                    </div>
                    <button onclick="updateCalibration()" style="background: #ffaa00; color: black; margin-right: 10px;">Update Calibration</button>
                    <button onclick="saveLogs()" style="background: #00ffaa; color: black;">Save Analysis Logs</button>
                </div>
                
                <div class="dashboard">
                    <div class="image-section">
                        <h2>📸 Live Detection</h2>
                        <div class="image-container">
                            <div class="image-box">
                                <h3>Original Inventory</h3>
                                <img id="originalImage" src="" alt="Original">
                            </div>
                            <div class="image-box">
                                <h3>MEGA Detection Results</h3>
                                <img id="resultImage" src="" alt="Detection">
                            </div>
                        </div>
                        
                        <div class="controls">
                            <button class="btn-toggle" onclick="toggleDetection()">
                                <span id="status">TOGGLE</span> DETECTION (F9)
                            </button>
                            <button class="btn-detect" onclick="forceDetection()">
                                FORCE DETECTION (F10)
                            </button>
                            <button class="btn-mega" onclick="toggleMega()">
                                TOGGLE MEGA (F11)
                            </button>
                        </div>
                    </div>
                    
                    <div class="stats-section">
                        <h2>📊 Stats</h2>
                        <div class="stat-grid">
                            <div class="stat-card">
                                <div class="stat-value" id="fps">0</div>
                                <div class="stat-label">FPS</div>
                            </div>
                            <div class="stat-card">
                                <div class="stat-value" id="detectionCount">0</div>
                                <div class="stat-label">Total Detections</div>
                            </div>
                        </div>
                        
                        <h3>🎯 Quick Guide</h3>
                        <div style="background: rgba(10,10,26,0.5); padding: 20px; border-radius: 10px; margin-top: 15px;">
                            <div style="margin-bottom: 10px;"><strong>F9</strong> - Toggle detection ON/OFF</div>
                            <div style="margin-bottom: 10px;"><strong>F10</strong> - Force immediate detection</div>
                            <div style="margin-bottom: 10px;"><strong>F11</strong> - Toggle MEGA mapping mode</div>
                            <div style="margin-bottom: 10px;"><strong>ESC</strong> - Exit program (saves logs)</div>
                            <div><strong>TAB</strong> - Open inventory in PUBG</div>
                        </div>
                    </div>
                </div>
                
                <div class="mappings-section">
                    <h2>🗺️ MEGA Mappings</h2>
                    <div class="mapping-columns">
                        <div class="mapping-column weapon-mapping">
                            <h4>🔫 Weapon to Slot</h4>
                            <div id="weaponMappings">
                                <div class="empty-state">No weapon mappings yet</div>
                            </div>
                        </div>
                        <div class="mapping-column scope-mapping">
                            <h4>🔭 Scope to Weapon to Slot</h4>
                            <div id="scopeMappings">
                                <div class="empty-state">No scope mappings yet</div>
                            </div>
                        </div>
                    </div>
                </div>
                
                <div class="detections-section">
                    <h2>🔍 Latest Detections</h2>
                    <div id="detections">
                        <div class="empty-state">Waiting for first detection...</div>
                    </div>
                </div>
                
                <footer>
                    <p>🎮 PUBG MEGA Detection AI | Model: YOLOv8 Custom Trained | Real-time FPS: <span id="fpsFooter">0</span></p>
                    <p>📁 Detection images saved to 'captures/' folder | MEGA debug to 'mega_debug/' folder</p>
                </footer>
            </div>
        </body>
        </html>
        """
        
        @self.app.route('/')
        def index():
            return render_template_string(HTML)
        
        @self.app.route('/api/status')
        def api_status():
            """Get current status - FIXED for JSON serialization"""
            # Convert images to base64
            result_b64 = None
            original_b64 = None
            
            if self.latest_result is not None:
                _, buffer = cv2.imencode('.png', self.latest_result)
                result_b64 = base64.b64encode(buffer).decode('utf-8')
            
            if self.latest_image is not None:
                _, buffer = cv2.imencode('.png', self.latest_image)
                original_b64 = base64.b64encode(buffer).decode('utf-8')
            
            # Helper function to convert numpy types to Python native types
            def convert_to_serializable(obj):
                if isinstance(obj, np.generic):
                    return obj.item()  # Convert numpy scalar to Python type
                elif isinstance(obj, dict):
                    return {key: convert_to_serializable(value) for key, value in obj.items()}
                elif isinstance(obj, list):
                    return [convert_to_serializable(item) for item in obj]
                elif isinstance(obj, tuple):
                    return tuple(convert_to_serializable(item) for item in obj)
                else:
                    return obj
            
            # Prepare data with serializable types
            weapon_mappings_serializable = convert_to_serializable(self.latest_mappings['weapon_slot'])
            scope_mappings_serializable = convert_to_serializable(self.latest_mappings['scope_slot'])
            scope_weapon_mappings_serializable = convert_to_serializable(self.latest_mappings['scope_weapon'])
            mapping_details_serializable = convert_to_serializable(self.latest_mappings['details'])
            
            # Convert detections
            detections_serializable = []
            for det in self.latest_detections:
                det_serializable = {
                    'class': det['class'],
                    'confidence': float(det['confidence']) if isinstance(det['confidence'], np.generic) else det['confidence'],
                    'type': det['type']
                }
                detections_serializable.append(det_serializable)
            
            # Return JSON-serializable data
            response_data = {
                'running': self.running,
                'fps': float(self.fps) if isinstance(self.fps, np.generic) else self.fps,
                'detection_count': int(self.detection_count),
                'detections': detections_serializable,
                'result_image': result_b64,
                'original_image': original_b64,
                'monitor': self.monitor,
                'mega_enabled': self.enable_mega_mapping,
                'weapon_mappings': weapon_mappings_serializable,
                'scope_mappings': scope_mappings_serializable,
                'scope_weapon_mappings': scope_weapon_mappings_serializable,
                'mapping_details': mapping_details_serializable,
                'timestamp': float(time.time())
            }
            
            return jsonify(response_data)
        
        @self.app.route('/api/toggle', methods=['POST'])
        def api_toggle():
            self.running = not self.running
            return jsonify({
                'message': f'Detection {"ACTIVATED" if self.running else "PAUSED"}',
                'running': self.running
            })
        
        @self.app.route('/api/toggle_mega', methods=['POST'])
        def api_toggle_mega():
            self.enable_mega_mapping = not self.enable_mega_mapping
            return jsonify({
                'message': f'MEGA mapping {"ENABLED" if self.enable_mega_mapping else "DISABLED"}',
                'mega_enabled': self.enable_mega_mapping
            })
        
        @self.app.route('/api/force', methods=['POST'])
        def api_force():
            # Force a detection
            self.perform_single_detection()
            return jsonify({
                'message': 'Forced detection complete',
                'success': True
            })
        
        @self.app.route('/api/calibrate', methods=['POST'])
        def api_calibrate():
            """Update calibration settings"""
            try:
                data = request.get_json()
                
                self.monitor['top'] = int(data.get('top', 100))
                self.monitor['left'] = int(data.get('left', 1300))
                self.monitor['width'] = int(data.get('width', 400))
                self.monitor['height'] = int(data.get('height', 600))
                
                return jsonify({
                    'message': f'Calibration updated: {self.monitor}',
                    'success': True,
                    'monitor': self.monitor
                })
            except Exception as e:
                return jsonify({
                    'message': f'Error: {e}',
                    'success': False
                })
        
        @self.app.route('/api/save_logs', methods=['POST'])
        def api_save_logs():
            """Save analysis logs"""
            try:
                log_files = self.save_analysis_logs()
                if log_files:
                    return jsonify({
                        'message': f'Logs saved: {log_files}',
                        'success': True,
                        'files': log_files
                    })
                else:
                    return jsonify({
                        'message': 'Failed to save logs',
                        'success': False
                    })
            except Exception as e:
                return jsonify({
                    'message': f'Error: {e}',
                    'success': False
                })
    
    def manual_calibration(self):
        """Manual calibration"""
        print("\n🎯 MANUAL CALIBRATION")
        print("=" * 50)
        print("1. Open PUBG and press TAB to show inventory")
        print("2. Make sure weapons and scopes are visible")
        print("3. We'll help you find the right area")
        print("\nCurrent settings:")
        print(f"   Top: {self.monitor['top']}")
        print(f"   Left: {self.monitor['left']}")
        print(f"   Width: {self.monitor['width']}")
        print(f"   Height: {self.monitor['height']}")
        
        adjust = input("\nAdjust settings? (y/n): ").strip().lower()
        
        if adjust == 'y':
            try:
                self.monitor['top'] = int(input(f"Top [{self.monitor['top']}]: ") or self.monitor['top'])
                self.monitor['left'] = int(input(f"Left [{self.monitor['left']}]: ") or self.monitor['left'])
                self.monitor['width'] = int(input(f"Width [{self.monitor['width']}]: ") or self.monitor['width'])
                self.monitor['height'] = int(input(f"Height [{self.monitor['height']}]: ") or self.monitor['height'])
                print("✅ Settings updated!")
            except:
                print("❌ Invalid input, keeping old settings")
        
        # Test capture
        print("\n📸 Testing capture...")
        test_img = self.capture_screen()
        
        if test_img is None:
            print("❌ Failed to capture! Check your settings.")
            return False
        
        # Save test image
        cv2.imwrite("calibration_test.png", test_img)
        print("✅ Test image saved to 'calibration_test.png'")
        
        # Test detection
        print("\n🤖 Testing MEGA detection...")
        result_img, detections, mapping_data = self.detect_with_mega_mapping(test_img)
        
        if result_img is not None:
            cv2.imwrite("calibration_mega.png", result_img)
            print("✅ MEGA detection result saved to 'calibration_mega.png'")
        
        if detections:
            print(f"✅ Found {len(detections)} objects!")
            for det in detections:
                print(f"  • {det['type'].upper()}: {det['class']} ({det['confidence']:.1%})")
            
            if mapping_data['weapon_mapping']:
                print("  🔫 Weapon mappings:")
                for weapon, slot in mapping_data['weapon_mapping'].items():
                    print(f"     ✅ {weapon} → {slot}")
            
            if mapping_data['scope_mapping']:
                print("  🔭 Scope mappings:")
                for scope, slot in mapping_data['scope_mapping'].items():
                    weapon = mapping_data['scope_weapon_mapping'].get(scope, {}).get('weapon', 'Unknown')
                    print(f"     🔭 {scope} → {weapon} → {slot}")
            
            return True
        else:
            print("❌ No detections! Adjust area and try again.")
            return False
    
    def start_web_server(self):
        """Start Flask in background"""
        thread = threading.Thread(
            target=lambda: self.app.run(
                host='0.0.0.0',
                port=5000,
                debug=False,
                use_reloader=False,
                threaded=True
            ),
            daemon=True
        )
        thread.start()
        print("🌐 Web dashboard: http://localhost:5000")
        print("   • Adjust calibration settings in the web interface")
        print("   • Check 'captures/' folder for saved images")
        print("   • Check 'mega_debug/' for MEGA mapping visualizations")
    
    def batch_process_images(self, folder_path="Test_Images"):
        """Process images in batch mode (for testing)"""
        print(f"\n📂 BATCH PROCESSING: {folder_path}")
        
        image_paths = []
        for ext in ['*.png', '*.jpg', '*.jpeg', '*.bmp']:
            image_paths.extend(glob.glob(os.path.join(folder_path, ext)))
        
        if not image_paths:
            print(f"❌ No images found in {folder_path}/")
            return
        
        print(f"✅ Found {len(image_paths)} images")
        
        all_results = []
        
        for i, image_path in enumerate(image_paths):
            print(f"\n📸 Processing {i+1}/{len(image_paths)}: {os.path.basename(image_path)}")
            
            img = cv2.imread(image_path)
            if img is None:
                print(f"   ❌ Failed to load")
                continue
            
            # Run detection
            result_img, detections, mapping_data = self.detect_with_mega_mapping(img)
            
            print(f"   🔫 Weapons: {len(mapping_data['weapons'])}")
            print(f"   🔢 Slots: {len(mapping_data['slots'])}")
            print(f"   🔭 Scopes: {len(mapping_data['scopes'])}")
            
            # Save results
            debug_filename = f"mega_debug/batch_{os.path.splitext(os.path.basename(image_path))[0]}.png"
            cv2.imwrite(debug_filename, result_img)
            print(f"   💾 Saved: {debug_filename}")
            
            all_results.append({
                'filename': os.path.basename(image_path),
                'mapping_data': mapping_data
            })
        
        print(f"\n✅ Batch processing complete: {len(all_results)} images")
        return all_results
    
    def run(self):
        """Start everything"""
        # Manual calibration
        if not self.manual_calibration():
            print("⚠️  Calibration failed. You can adjust in web interface.")
        
        # Start web server
        self.start_web_server()
        
        print("\n" + "=" * 70)
        print("🔥 MEGA PUBG DETECTOR READY!")
        print("=" * 70)
        print("🎮 IN-GAME CONTROLS:")
        print("  1. Press TAB to show inventory")
        print("  2. Press F9 to start/stop detection")
        print("  3. Press F10 to force detection")
        print("  4. Press F11 to toggle MEGA mapping")
        print("  5. Press ESC to exit (saves logs)")
        print("\n🌐 WEB DASHBOARD:")
        print("  • Open http://localhost:5000 in browser")
        print("  • See real-time weapon & scope mappings")
        print("  • Adjust calibration if needed")
        print("  • View saved images in 'captures/' and 'mega_debug/'")
        print("\n📊 FEATURES:")
        print("  • Real-time weapon detection")
        print("  • Advanced slot mapping")
        print("  • Scope-to-weapon mapping")
        print("  • MEGA visualization")
        print("  • Performance logging")
        print("=" * 70)
        
        # Run detection loop
        self.run_detection_loop()

# ============================================================================
# MAIN EXECUTION
# ============================================================================

if __name__ == "__main__":
    print("=" * 70)
    print("🎮 PUBG MEGA REAL-TIME DETECTOR")
    print("=" * 70)
    print("\n🔥 COMBINED FEATURES:")
    print("   1️⃣ Real-time screen capture")
    print("   2️⃣ YOLOv8 weapon & scope detection")
    print("   3️⃣ MEGA mapping algorithm")
    print("   4️⃣ Scope-to-weapon association")
    print("   5️⃣ Web dashboard interface")
    print("   6️⃣ Performance logging")
    print("=" * 70)
    
    # Ask for model path
    model_path = input("\nEnter model path (default: yolov8n.pt): ").strip()
    if not model_path:
        model_path = "best.pt"
    
    # Ask for batch processing
    batch_mode = input("\nProcess test images first? (y/n, default: n): ").strip().lower()
    
    detector = MEGAPUBGRealtimeDetector(model_path)
    
    if batch_mode == 'y':
        folder = input("Enter folder path (default: Test_Images): ").strip()
        if not folder:
            folder = "Test_Images"
        detector.batch_process_images(folder)
    
    # Start real-time detection
    detector.run()