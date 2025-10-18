import random
import re
import tkinter as tk
from tkinter import messagebox
from tkinter import ttk
import threading
import queue
from dataclasses import dataclass, field
from typing import List, Dict, Optional, Tuple

# ------------------------------------------------------------
# Data Models
# ------------------------------------------------------------
@dataclass
class Course:
    id: str
    name: str
    instructor_name: str
    students: int
    periods_per_week: int
    cohort_ids: List[str]
    course_type: str = "lecture"
    requires_consecutive: int = 1
    lab_must_be_after_lec: bool = False

@dataclass
class Room:
    name: str
    capacity: int
    room_type: str = "lecture"
    unavailable_times: List[str] = field(default_factory=list)

@dataclass
class Instructor:
    name: str
    unavailable_times: List[str]
    preferred: str = ""

# ------------------------------------------------------------
# GA Timetable
# ------------------------------------------------------------
class EasyTimetableGA:
    def __init__(self, courses: List[Course], instructors: List[Instructor], rooms: List[Room]):
        self.courses = courses
        self.instructors: Dict[str, Instructor] = {inst.name: inst for inst in instructors}
        self.rooms = rooms
        self.rooms_map: Dict[str, Room] = {r.name: r for r in rooms}
        self.course_map: Dict[str, Course] = {c.id: c for c in courses}
        self.days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']
        self.times = ['08:00', '09:00', '10:00', '11:00', '13:00', '14:00', '15:00', '16:00']
        self.time_index = {t: i for i, t in enumerate(self.times)}
        self.lunch_break_index = self.time_index.get('11:00')
        self.morning_times = set(self.times[:4])
        self.afternoon_times = set(self.times[4:])
        self.weights = {
            'instr_conflict': 15, 'room_conflict': 15, 'cohort_conflict': 20,
            'unavailable': 20, 'over_capacity': 10, 'wrong_room_type': 12,
            'same_course_same_day': 5, 'consecutive_bonus': 8, 'consecutive_penalty': 10,
            'pref_bonus': 2, 'pref_penalty': 2, 'linked_course_same_day': 25,
            'room_unavailable': 20, 'lab_before_lec': 15,
        }
        self.linked_min_days_default = 2
        self.compatible_rooms: Dict[str, List[Room]] = {
            c.id: [r for r in rooms if r.room_type == c.course_type and r.capacity >= c.students]
            for c in courses
        }
        self.HEURISTIC_PLACEMENT_ATTEMPTS = 50

    def _base_id(self, cid: str) -> str:
        return cid.rsplit('_', 1)[0]

    def _validate_inputs(self):
        for c in self.courses:
            if c.requires_consecutive > c.periods_per_week:
                raise ValueError(f"Course '{c.name}': consecutive requirement > periods per week.")
            if c.students <= 0: raise ValueError(f"Course '{c.name}': students must be > 0.")
            if not self.compatible_rooms[c.id]:
                raise ValueError(f"Course '{c.name}' (ID: {c.id}) has no compatible rooms available.")
        for r in self.rooms:
            if r.capacity <= 0: raise ValueError(f"Room '{r.name}' capacity must be > 0.")

    def has_run_at_least(self, sorted_idx, run_len):
        if run_len <= 1: return True
        if not sorted_idx or len(sorted_idx) < run_len: return False
        cur = 1
        for a, b in zip(sorted_idx, sorted_idx[1:]):
            if b - a == 1 and (self.lunch_break_index is None or a != self.lunch_break_index):
                cur += 1
                if cur >= run_len: return True
            else: cur = 1
        return False
        
    def _neighbor_times(self, time: str, *, exclude_self=False) -> List[str]:
        i = self.time_index.get(time, -1);
        if i == -1: return []
        out = []
        if i > 0: out.append(self.times[i-1])
        if not exclude_self: out.append(time)
        if i < len(self.times) - 1: out.append(self.times[i+1])
        return out or ([time] if not exclude_self else [])

    def _biased_time_choices(self, course: Course, day: str):
        base = list(self.times)
        inst = self.instructors.get(course.instructor_name)
        if inst:
            pref = (inst.preferred or "").lower()
            if pref == "morning":   base = self.times[:4]*3 + self.times[4:]
            elif pref == "afternoon": base = self.times[4:]*3 + self.times[:4]
            unav = {t.split()[1] for t in inst.unavailable_times if t.startswith(day + " ")}
            base = [t for t in base if t not in unav] or list(self.times)
        return base

    def _try_place_block(self, occ, course, day, start_idx, room):
        need = course.requires_consecutive
        if start_idx + need > len(self.times): return None
        if self.lunch_break_index is not None and start_idx <= self.lunch_break_index and start_idx + need > self.lunch_break_index + 1:
            return None
        slots = []
        for k in range(need):
            t = self.times[start_idx + k]; ts = f"{day} {t}"
            if (ts in occ['instr'].get(course.instructor_name, set()) or
                ts in occ['room'].get(room.name, set()) or
                any(ts in occ['cohort'].get(cid, set()) for cid in course.cohort_ids)):
                return None
            slots.append((t, ts))
        for _, ts in slots:
            occ['instr'].setdefault(course.instructor_name, set()).add(ts)
            occ['room'].setdefault(room.name, set()).add(ts)
            for cid in course.cohort_ids:
                occ['cohort'].setdefault(cid, set()).add(ts)
        return [{'class_id': f"{course.id}_period{k+1}", 'course_id': course.id, 'day': day, 'time': t, 'room': room.name}
                for k, (t, _) in enumerate(slots)]

    def create_heuristic_schedule(self) -> List[Dict]:
        schedule, occupancy = [], {'instr': {}, 'room': {}, 'cohort': {}}
        sorted_courses = sorted(self.courses, key=lambda c: (len(self.compatible_rooms[c.id]), -c.requires_consecutive, -c.students))
        for course in sorted_courses:
            placed_periods = 0
            if course.requires_consecutive > 1:
                for _ in range(20):
                    day, room = random.choice(self.days), random.choice(self.compatible_rooms[course.id])
                    start_idx = random.randrange(len(self.times) - course.requires_consecutive + 1)
                    block = self._try_place_block(occupancy, course, day, start_idx, room)
                    if block: schedule.extend(block); placed_periods = course.requires_consecutive; break
            
            remaining_periods = range(placed_periods + 1, course.periods_per_week + 1)
            for p_num in remaining_periods:
                class_id = f"{course.id}_period{p_num}"; placed = False
                for _ in range(self.HEURISTIC_PLACEMENT_ATTEMPTS):
                    day, time, room = random.choice(self.days), random.choice(self._biased_time_choices(course, day)), random.choice(self.compatible_rooms[course.id])
                    tslot = f"{day} {time}"
                    if (tslot not in occupancy['instr'].get(course.instructor_name, set()) and
                        tslot not in occupancy['room'].get(room.name, set()) and
                        tslot not in room.unavailable_times and
                        not any(tslot in occupancy['cohort'].get(cid, set()) for cid in course.cohort_ids)):
                        occupancy['instr'].setdefault(course.instructor_name, set()).add(tslot)
                        occupancy['room'].setdefault(room.name, set()).add(tslot)
                        for cid in course.cohort_ids:
                            occupancy['cohort'].setdefault(cid, set()).add(tslot)
                        schedule.append({'class_id': class_id, 'course_id': course.id, 'day': day, 'time': time, 'room': room.name}); placed = True; break
                if not placed:
                    room, day, time = random.choice(self.compatible_rooms[course.id]), random.choice(self.days), random.choice(self.times)
                    tslot = f"{day} {time}"
                    occupancy['instr'].setdefault(course.instructor_name, set()).add(tslot)
                    occupancy['room'].setdefault(room.name, set()).add(tslot)
                    for cid in course.cohort_ids:
                        occupancy['cohort'].setdefault(cid, set()).add(tslot)
                    schedule.append({'class_id': class_id, 'course_id': course.id, 'day': day, 'time': time, 'room': room.name})
        return schedule

    def check_fitness(self, schedule: List[Dict]) -> float:
        score = 100.0
        occupancy, per_course_day = {'instr': {}, 'room': {}, 'cohort': {}}, {}
        for cl_info in schedule:
            course = self.course_map[cl_info['course_id']]; tslot = f"{cl_info['day']} {cl_info['time']}"
            inst, room_name = course.instructor_name, cl_info['room']
            if tslot in occupancy['instr'].setdefault(inst, set()): score -= self.weights['instr_conflict']
            else: occupancy['instr'][inst].add(tslot)
            if tslot in occupancy['room'].setdefault(room_name, set()): score -= self.weights['room_conflict']
            else: occupancy['room'][room_name].add(tslot)
            for cohort_id in course.cohort_ids:
                if tslot in occupancy['cohort'].setdefault(cohort_id, set()): score -= self.weights['cohort_conflict']
                else: occupancy['cohort'][cohort_id].add(tslot)
            if inst in self.instructors:
                if tslot in self.instructors[inst].unavailable_times: score -= self.weights['unavailable']
                pref = (self.instructors[inst].preferred or "").lower()
                if pref == "morning": score += self.weights['pref_bonus'] if cl_info['time'] in self.morning_times else -self.weights['pref_penalty']
                elif pref == "afternoon": score += self.weights['pref_bonus'] if cl_info['time'] in self.afternoon_times else -self.weights['pref_penalty']
            room = self.rooms_map.get(room_name)
            if room:
                if tslot in room.unavailable_times: score -= self.weights['room_unavailable']
                if room.room_type != course.course_type: score -= self.weights['wrong_room_type']
                if room.capacity < course.students: score -= self.weights['over_capacity'] * (1 + (course.students - room.capacity) / max(1, room.capacity))
            per_course_day.setdefault((cl_info['course_id'], cl_info['day']), []).append(self.time_index[cl_info['time']])
        
        for (course_id, day), idx_list in per_course_day.items():
            course = self.course_map[course_id]; idx_list.sort()
            if course.requires_consecutive > 1:
                score += self.weights['consecutive_bonus'] if self.has_run_at_least(idx_list, course.requires_consecutive) else -self.weights['consecutive_penalty']
            if len(idx_list) > course.requires_consecutive:
                score -= self.weights['same_course_same_day'] * (len(idx_list) - course.requires_consecutive)

        linked_courses = {}
        for course_id in self.course_map: linked_courses.setdefault(self._base_id(course_id), []).append(course_id)
        
        days_by_cid = {}
        for (cid, day), idx_list in per_course_day.items():
            if idx_list: days_by_cid.setdefault(cid, set()).add(day)
        day_indices = {day: i for i, day in enumerate(self.days)}

        for base_id, group in linked_courses.items():
            if len(group) < 2: continue
            days_used = {day for cid in group if cid in days_by_cid for day in days_by_cid[cid]}
            required = min(len(group), self.linked_min_days_default)
            if len(days_used) < required: score -= self.weights['linked_course_same_day']
            
            lec_course_id = next((c for c in group if self.course_map[c].lab_must_be_after_lec), None)
            if lec_course_id:
                lab_course_id = next((c for c in group if 'Lab' in c), None) # Simple assumption
                lec_days = days_by_cid.get(lec_course_id, set())
                lab_days = days_by_cid.get(lab_course_id, set())
                if lec_days and lab_days:
                    max_lec_day_idx = max(day_indices.get(d, -1) for d in lec_days)
                    min_lab_day_idx = min(day_indices.get(d, -1) for d in lab_days)
                    if max_lec_day_idx > min_lab_day_idx:
                        score -= self.weights['lab_before_lec']
        return max(0.0, score)

    def select_parent(self, population, fitness_scores):
        k = min(3, len(population)); cand_idx = random.sample(range(len(population)), k)
        return population[max(cand_idx, key=fitness_scores.__getitem__)]

    def _check_gene_conflict(self, gene: Dict, occupancy: Dict) -> bool:
        course = self.course_map[gene['course_id']]; ts = f"{gene['day']} {gene['time']}"
        return (ts in occupancy['instr'].get(course.instructor_name, set()) or
                ts in occupancy['room'].get(gene['room'], set()) or
                any(ts in occupancy['cohort'].get(cid, set()) for cid in course.cohort_ids))

    def _update_occupancy(self, gene: Dict, occupancy: Dict):
        course = self.course_map[gene['course_id']]; ts = f"{gene['day']} {gene['time']}"
        occupancy['instr'].setdefault(course.instructor_name, set()).add(ts)
        occupancy['room'].setdefault(gene['room'], set()).add(ts)
        for cid in course.cohort_ids:
            occupancy['cohort'].setdefault(cid, set()).add(ts)

    def greedy_crossover(self, p1: List[Dict], p2: List[Dict]) -> List[Dict]:
        m1 = {g['class_id']: g for g in p1}
        m2 = {g['class_id']: g for g in p2}
        child, occ = [], {'instr': {}, 'room': {}, 'cohort': {}}
        for cid in m1:
            # --- ส่วนที่แก้ไข ---
            g1 = m1[cid]
            g2 = m2.get(cid, g1) # ใช้ g1 เป็น default หลังจากที่ g1 ถูกสร้างแล้ว
            # --- สิ้นสุดส่วนที่แก้ไข ---
            
            conflict1 = self._check_gene_conflict(g1, occ)
            conflict2 = self._check_gene_conflict(g2, occ)
            
            if not conflict1 and (conflict2 or random.random() < 0.5):
                selected = g1
            elif not conflict2:
                selected = g2
            else:
                selected = g1
                
            child.append(dict(selected))
            self._update_occupancy(selected, occ)
        return child

    def mutate(self, sched, rate=0.1):
        for i in range(len(sched)):
            if random.random() < rate:
                gene, course = random.choice(['day', 'time', 'room']), self.course_map[sched[i]['course_id']]
                if gene == 'room': sched[i]['room'] = random.choice(self.compatible_rooms[course.id]).name
                elif gene == 'day': sched[i]['day'] = random.choice(self.days)
                elif gene == 'time': sched[i]['time'] = random.choice(self._biased_time_choices(course, sched[i]['day']))
        return sched
    
    def _repair(self, sched):
        for x in sched:
            course, room = self.course_map[x['course_id']], self.rooms_map.get(x['room'])
            if not room or room.room_type != course.course_type or room.capacity < course.students:
                x['room'] = random.choice(self.compatible_rooms[course.id]).name
        return sched
    
    def _is_part_of_good_run(self, schedule, class_info, run_cache):
        course_id, day = class_info['course_id'], class_info['day']; key = (course_id, day)
        if key in run_cache: return run_cache[key]
        course = self.course_map[course_id]
        if course.requires_consecutive <= 1: run_cache[key] = True; return True
        indices = sorted([self.time_index[x['time']] for x in schedule if x['course_id'] == course_id and x['day'] == day])
        result = self.has_run_at_least(indices, course.requires_consecutive); run_cache[key] = result; return result

    def _snap_to_run_time(self, schedule, class_info):
        course_id, day = class_info['course_id'], class_info['day']; course = self.course_map[course_id]
        if course.requires_consecutive <= 1: return None
        other_indices = sorted([self.time_index[x['time']] for x in schedule if x['course_id'] == course_id and x['day'] == day and x is not class_info])
        if not other_indices: return None
        for start in range(len(self.times) - course.requires_consecutive + 1):
            if self.lunch_break_index is not None and start <= self.lunch_break_index < start + course.requires_consecutive: continue
            required_block = set(range(start, start + course.requires_consecutive))
            missing_indices = list(required_block - set(other_indices))
            if len(missing_indices) == 1: return self.times[missing_indices[0]]
        return None

    def _repair_conflicts(self, sched):
        good_genes, bad_genes, seen_keys, run_cache = [], [], [set(), set(), set()], {}
        for x in sched:
            ts = f"{x['day']} {x['time']}"; course = self.course_map[x['course_id']]
            keys = ((course.instructor_name, ts), (x['room'], ts))
            is_conflicted = keys[0] in seen_keys[0] or keys[1] in seen_keys[1] or any((cid, ts) in seen_keys[2] for cid in course.cohort_ids)
            is_good_run = self._is_part_of_good_run(sched, x, run_cache) if course.requires_consecutive > 1 else True
            if not is_conflicted and is_good_run:
                seen_keys[0].add(keys[0]); seen_keys[1].add(keys[1])
                for cid in course.cohort_ids: seen_keys[2].add((cid, ts))
                good_genes.append(x)
            else: bad_genes.append(x)
        repaired_genes = []
        for x in bad_genes:
            course = self.course_map[x['course_id']]; fixed = False
            snapped_time = self._snap_to_run_time(sched, x)
            if snapped_time:
                ts = f"{x['day']} {snapped_time}"; keys = ((course.instructor_name, ts), (x['room'], ts))
                if not (keys[0] in seen_keys[0] or keys[1] in seen_keys[1] or any((cid, ts) in seen_keys[2] for cid in course.cohort_ids)):
                    x['time'] = snapped_time; fixed = True
                    seen_keys[0].add(keys[0]); seen_keys[1].add(keys[1])
                    for cid in course.cohort_ids: seen_keys[2].add((cid, ts))
            if not fixed:
                for _ in range(4):
                    neighbors = self._neighbor_times(x['time'], exclude_self=True)
                    if not neighbors: continue
                    x['time'] = random.choice(neighbors)
                    ts = f"{x['day']} {x['time']}"; keys = ((course.instructor_name, ts), (x['room'], ts))
                    if not (keys[0] in seen_keys[0] or keys[1] in seen_keys[1] or any((cid, ts) in seen_keys[2] for cid in course.cohort_ids)):
                        seen_keys[0].add(keys[0]); seen_keys[1].add(keys[1])
                        for cid in course.cohort_ids: seen_keys[2].add((cid, ts))
                        fixed = True; break
            if not fixed:
                original_day = x['day']
                for _ in range(4):
                    x['day'] = random.choice(self.days)
                    ts = f"{x['day']} {x['time']}"; keys = ((course.instructor_name, ts), (x['room'], ts))
                    if not (keys[0] in seen_keys[0] or keys[1] in seen_keys[1] or any((cid, ts) in seen_keys[2] for cid in course.cohort_ids)):
                        seen_keys[0].add(keys[0]); seen_keys[1].add(keys[1])
                        for cid in course.cohort_ids: seen_keys[2].add((cid, ts))
                        fixed = True; break
                if not fixed: x['day'] = original_day
            repaired_genes.append(x)
        return good_genes + repaired_genes

    def evolve(self, population_size=80, generations=1000, mutate_rate=0.2, patience=120, elitism=5, seed: Optional[int]=None, cancel_flag=None):
        if seed is not None: random.seed(seed)
        self._validate_inputs()
        population = [self.create_heuristic_schedule() for _ in range(population_size)]
        best_ever_score, stale_generations = -float('inf'), 0; best_schedule = population[0]
        immigrants = max(1, population_size // 20)
        for gen in range(generations):
            if cancel_flag and cancel_flag.is_set(): print("\n⛔️ Operation cancelled by user."); break
            fitness = [self.check_fitness(s) for s in population]
            current_best_idx = max(range(len(fitness)), key=fitness.__getitem__)
            current_best_score = fitness[current_best_idx]
            if current_best_score > best_ever_score:
                best_ever_score, best_schedule, stale_generations = current_best_score, population[current_best_idx], 0
            else: stale_generations += 1
            if gen % 50 == 0: print(f"Generation {gen}: Best Score = {best_ever_score:.1f} (Stagnant for {stale_generations} gens)")
            if stale_generations >= patience and best_ever_score > 0: print(f"✅ Stopping at generation {gen} due to stagnation (Best: {best_ever_score:.1f})"); break
            sorted_pop = sorted(zip(population, fitness), key=lambda x: x[1], reverse=True)
            pop_new = [p for p, _ in sorted_pop[:elitism]]
            while len(pop_new) < population_size - immigrants:
                p1, p2 = self.select_parent(population, fitness), self.select_parent(population, fitness)
                child = self._repair_conflicts(self._repair(self.mutate(self.greedy_crossover(p1, p2), mutate_rate)))
                pop_new.append(child)
            for _ in range(immigrants): pop_new.append(self.create_heuristic_schedule())
            population = pop_new
        return best_schedule

    def show_grid(self, root, schedule: List[Dict]):
        win = tk.Toplevel(root); win.title("Timetable (Grid)"); table = tk.Frame(win); table.pack(fill=tk.BOTH, expand=True)
        tk.Label(table, text="", borderwidth=1, relief="solid").grid(row=0, column=0, sticky="nsew")
        for c, day in enumerate(self.days, start=1): tk.Label(table, text=day, borderwidth=1, relief="solid", font=("", 10, "bold")).grid(row=0, column=c, sticky="nsew")
        cell = {(d, t): [] for d in self.days for t in self.times}
        for cl_info in schedule:
            course = self.course_map[cl_info['course_id']]
            cell[(cl_info['day'], cl_info['time'])].append({'course': course, 'room': cl_info['room']})
        for r in range(len(self.times) + 1): table.grid_rowconfigure(r, weight=1)
        for c in range(len(self.days) + 1): table.grid_columnconfigure(c, weight=1)
        win.update_idletasks(); wrap = max(180, int(win.winfo_width() / (len(self.days)+1)) - 20)
        for r, t in enumerate(self.times, start=1):
            tk.Label(table, text=f"{t}", borderwidth=1, relief="solid").grid(row=r, column=0, sticky="nsew")
            for c, d in enumerate(self.days, start=1):
                items = cell[(d, t)]; bg, txt = "#ffffff", ""
                if items:
                    is_multi_slot = len(items) > 1
                    cohorts = [it['course'].cohort_ids for it in items]
                    insts, rooms = [it['course'].instructor_name for it in items], [it['room'] for it in items]
                    all_cohorts = [item for sublist in cohorts for item in sublist]
                    has_hard_conflict = is_multi_slot and (len(set(all_cohorts)) < len(all_cohorts) or len(set(insts)) < len(items) or len(set(rooms)) < len(items))
                    bg = "#ffcccc" if has_hard_conflict else ("#ffebcc" if is_multi_slot else "#e8f4ff")
                    txt = "\n".join(f"{it['course'].name}\n({', '.join(it['course'].cohort_ids)})\n{it['course'].instructor_name} • {it['room']}" for it in items)
                lbl = tk.Label(table, text=txt, borderwidth=1, relief="solid", justify="left", anchor="nw", padx=6, pady=6, bg=bg, wraplength=wrap)
                lbl.grid(row=r, column=c, sticky="nsew")

# ------------------------------------------------------------
# Sample Data, UI, and Main Execution
# ------------------------------------------------------------
def create_easy_data():
    instructors = [
        Instructor("Inst. Sombat", [], ""), Instructor("Inst. Jintana", [], "morning"),
        Instructor("Inst. Wichan", ["Friday 08:00", "Friday 09:00"], "morning"), Instructor("Inst. Somying", [], "afternoon"),
        Instructor("Inst. Prapai", [], "afternoon"),
    ]
    rooms = [
        Room("LEC101", 100, "lecture", unavailable_times=["Wednesday 13:00", "Wednesday 14:00"]), 
        Room("LEC202", 50, "lecture"), Room("LAB301", 30, "lab"), Room("LAB302", 30, "lab"),
        Room("LAB303", 50, "lab"),
    ]
    courses = [
        Course("CS101_Lec", "Intro to CS (Lec)", "Inst. Sombat", 60, 2, ['Y1_CS_A', 'Y1_CS_B'], "lecture", 2, lab_must_be_after_lec=True),
        Course("CS101_LabA", "Intro to CS (Lab A)", "Inst. Sombat", 30, 2, ['Y1_CS_A'], "lab", 2),
        Course("CS101_LabB", "Intro to CS (Lab B)", "Inst. Jintana", 30, 2, ['Y1_CS_B'], "lab", 2),
        Course("CS202_Lec", "Data Structures (Lec)", "Inst. Wichan", 45, 2, ['Y2_CS'], "lecture", 2),
        Course("CS202_Lab", "Data Structures (Lab)", "Inst. Wichan", 45, 2, ['Y2_CS'], "lab", 2),
        Course("EN101_Lec", "General English", "Inst. Somying", 60, 2, ['Y1_CS_A', 'Y1_CS_B'], "lecture", 2),
    ]
    return courses, instructors, rooms

class DataEntryUI(tk.Toplevel):
    def __init__(self, master, days, times):
        super().__init__(master); self.title("Timetable GA (University Pro)"); self.geometry("1250x720")
        self.days, self.times = days, times; self.instructors, self.rooms, self.courses = [], [], []
        
        topbar = tk.Frame(self); topbar.pack(fill=tk.X, padx=10, pady=10)
        tk.Button(topbar, text="Load Sample Data", command=self.load_sample).pack(side=tk.LEFT)
        tk.Label(topbar, text="Pop:").pack(side=tk.LEFT, padx=(10,0)); self.pop_var = tk.IntVar(value=100); tk.Spinbox(topbar, from_=20, to=500, textvariable=self.pop_var, width=5).pack(side=tk.LEFT)
        tk.Label(topbar, text="Gen:").pack(side=tk.LEFT, padx=(10,0)); self.gen_var = tk.IntVar(value=1000); tk.Spinbox(topbar, from_=100, to=5000, textvariable=self.gen_var, width=6).pack(side=tk.LEFT)
        tk.Label(topbar, text="Mutate:").pack(side=tk.LEFT, padx=(10,0)); self.mut_var = tk.DoubleVar(value=0.2); tk.Spinbox(topbar, from_=0.01, to=1.0, increment=0.01, textvariable=self.mut_var, width=5).pack(side=tk.LEFT)
        tk.Label(topbar, text="Patience:").pack(side=tk.LEFT, padx=(10,0)); self.patience_var = tk.IntVar(value=150); tk.Spinbox(topbar, from_=20, to=500, textvariable=self.patience_var, width=5).pack(side=tk.LEFT)
        tk.Label(topbar, text="Seed:").pack(side=tk.LEFT, padx=(10,0)); self.seed_var = tk.StringVar(value=""); tk.Entry(topbar, textvariable=self.seed_var, width=6).pack(side=tk.LEFT)
        self.generate_btn = tk.Button(topbar, text="🚀 Generate", command=self.on_generate, bg="#1e90ff", fg="white", font=("", 10, "bold")); self.generate_btn.pack(side=tk.LEFT, padx=10)
        self._cancel_flag = threading.Event()
        self.cancel_btn = tk.Button(topbar, text="Cancel", command=lambda: self._cancel_flag.set(), bg="#ffaaaa", state="disabled"); self.cancel_btn.pack(side=tk.LEFT)
        
        nb = ttk.Notebook(self); nb.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        tabs = {"👨‍🏫 Instructors": self.build_instructors_tab, "🚪 Rooms": self.build_rooms_tab, "📚 Courses": self.build_courses_tab}
        for name, builder in tabs.items(): tab = tk.Frame(nb); nb.add(tab, text=name); builder(tab)
        self.update_course_instructor_options(); self.queue = queue.Queue()

    def build_instructors_tab(self, parent):
        left = tk.Frame(parent); left.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5); right = tk.Frame(parent); right.pack(side=tk.LEFT, fill=tk.Y, padx=5, pady=5)
        cols = ("name", "preferred", "unav_count"); self.inst_tree = ttk.Treeview(left, columns=cols, show="headings")
        self.inst_tree.heading("name", text="Instructor Name"); self.inst_tree.heading("preferred", text="Preference"); self.inst_tree.heading("unav_count", text="Unavailable (#)"); self.inst_tree.pack(fill=tk.BOTH, expand=True, pady=5)
        self.inst_tree.bind("<<TreeviewSelect>>", self.on_inst_select)
        btns = tk.Frame(left); btns.pack(fill=tk.X, pady=5); tk.Button(btns, text="Add/Update", command=self.add_update_instructor).pack(side=tk.LEFT); tk.Button(btns, text="Delete", command=self.delete_instructor).pack(side=tk.LEFT, padx=5); tk.Button(btns, text="Clear Form", command=self.clear_inst_form).pack(side=tk.LEFT)
        tk.Label(right, text="Instructor Name").pack(anchor="w"); self.inst_name_var = tk.StringVar(); tk.Entry(right, textvariable=self.inst_name_var, width=30).pack(pady=(0,5))
        tk.Label(right, text="Time Preference").pack(anchor="w"); self.inst_pref_var = tk.StringVar(value=""); ttk.Combobox(right, textvariable=self.inst_pref_var, values=["", "morning", "afternoon"], state="readonly").pack(pady=(0,5))
        tk.Label(right, text="Unavailable Times").pack(anchor="w", pady=(10,0)); grid = tk.Frame(right, borderwidth=1, relief="groove"); grid.pack(); self.inst_unav_vars = {}
        for c, d in enumerate(self.days): tk.Label(grid, text=d[:3]).grid(row=0, column=c+1)
        for r, t in enumerate(self.times): tk.Label(grid, text=t).grid(row=r+1, column=0)
        for r, t in enumerate(self.times):
            for c, d in enumerate(self.days): var=tk.BooleanVar(); tk.Checkbutton(grid, variable=var).grid(row=r+1, column=c+1); self.inst_unav_vars[(d,t)] = var

    def build_rooms_tab(self, parent):
        left = tk.Frame(parent); left.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5); right = tk.Frame(parent); right.pack(side=tk.LEFT, fill=tk.Y, padx=5, pady=5)
        cols = ("name", "capacity", "type", "unav_count"); self.room_tree = ttk.Treeview(left, columns=cols, show="headings")
        self.room_tree.heading("name", text="Room Name"); self.room_tree.heading("capacity", text="Capacity"); self.room_tree.heading("type", text="Type"); self.room_tree.heading("unav_count", text="Unavailable (#)"); self.room_tree.pack(fill=tk.BOTH, expand=True, pady=5)
        self.room_tree.bind("<<TreeviewSelect>>", self.on_room_select)
        btns = tk.Frame(left); btns.pack(fill=tk.X, pady=5); tk.Button(btns, text="Add/Update", command=self.add_update_room).pack(side=tk.LEFT); tk.Button(btns, text="Delete", command=self.delete_room).pack(side=tk.LEFT, padx=5); tk.Button(btns, text="Clear Form", command=self.clear_room_form).pack(side=tk.LEFT)
        tk.Label(right, text="Room Name").pack(anchor="w"); self.room_name_var = tk.StringVar(); tk.Entry(right, textvariable=self.room_name_var, width=30).pack(pady=(0,5))
        tk.Label(right, text="Capacity").pack(anchor="w"); self.room_cap_var = tk.IntVar(value=30); tk.Spinbox(right, from_=1, to=500, textvariable=self.room_cap_var).pack(pady=(0,5))
        tk.Label(right, text="Room Type").pack(anchor="w"); self.room_type_var = tk.StringVar(value="lecture"); ttk.Combobox(right, textvariable=self.room_type_var, values=["lecture", "lab"], state="readonly").pack(pady=(0,5))
        tk.Label(right, text="Unavailable Times").pack(anchor="w", pady=(10,0)); grid = tk.Frame(right, borderwidth=1, relief="groove"); grid.pack(); self.room_unav_vars = {}
        for c, d in enumerate(self.days): tk.Label(grid, text=d[:3]).grid(row=0, column=c+1)
        for r, t in enumerate(self.times): tk.Label(grid, text=t).grid(row=r+1, column=0)
        for r, t in enumerate(self.times):
            for c, d in enumerate(self.days): var=tk.BooleanVar(); tk.Checkbutton(grid, variable=var).grid(row=r+1, column=c+1); self.room_unav_vars[(d,t)] = var

    def build_courses_tab(self, parent):
        left = tk.Frame(parent); left.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5); right = tk.Frame(parent); right.pack(side=tk.LEFT, fill=tk.Y, padx=5, pady=5)
        cols = ("id", "name", "inst", "cohort", "type", "students", "periods", "consecutive"); self.course_tree = ttk.Treeview(left, columns=cols, show="headings")
        for col, width, anchor in [("id",80,'w'), ("name",150,'w'), ("inst",120,'w'), ("cohort",100,'w'), ("type",60,'w'), ("students",60,'center'), ("periods",60,'center'), ("consecutive",60,'center')]:
            self.course_tree.heading(col, text=col.capitalize()); self.course_tree.column(col, width=width, anchor=anchor)
        self.course_tree.pack(fill=tk.BOTH, expand=True, pady=5); self.course_tree.bind("<<TreeviewSelect>>", self.on_course_select)
        btns = tk.Frame(left); btns.pack(fill=tk.X, pady=5); tk.Button(btns, text="Add/Update", command=self.add_update_course).pack(side=tk.LEFT); tk.Button(btns, text="Delete", command=self.delete_course).pack(side=tk.LEFT, padx=5); tk.Button(btns, text="Clear Form", command=self.clear_course_form).pack(side=tk.LEFT)
        form = tk.Frame(right); form.pack()
        tk.Label(form, text="Course ID (e.g., CS101_Lec)").grid(row=0, column=0, sticky="w"); self.course_id_var = tk.StringVar(); tk.Entry(form, textvariable=self.course_id_var).grid(row=1, column=0, columnspan=2, sticky="ew", pady=(0,5))
        tk.Label(form, text="Course Name").grid(row=2, column=0, sticky="w"); self.course_name_var = tk.StringVar(); tk.Entry(form, textvariable=self.course_name_var, width=30).grid(row=3, column=0, columnspan=2, sticky="ew", pady=(0,5))
        tk.Label(form, text="Instructor").grid(row=4, column=0, sticky="w"); self.course_inst_var = tk.StringVar(); self.inst_combo = ttk.Combobox(form, textvariable=self.course_inst_var, state="readonly"); self.inst_combo.grid(row=5, column=0, columnspan=2, sticky="ew", pady=(0,5))
        tk.Label(form, text="Cohort IDs (comma-separated)").grid(row=6, column=0, sticky="w"); self.course_cohort_var = tk.StringVar(); tk.Entry(form, textvariable=self.course_cohort_var).grid(row=7, column=0, columnspan=2, sticky='ew', pady=(0,5))
        tk.Label(form, text="Students").grid(row=8, column=0, sticky="w"); self.course_stud_var = tk.IntVar(value=30); tk.Spinbox(form, from_=1, to=500, textvariable=self.course_stud_var, width=10).grid(row=9, column=0, sticky='w', pady=(0,5))
        tk.Label(form, text="Course Type").grid(row=8, column=1, sticky="w"); self.course_type_var = tk.StringVar(value="lecture"); ttk.Combobox(form, textvariable=self.course_type_var, values=["lecture", "lab"], state="readonly", width=10).grid(row=9, column=1, sticky='w', pady=(0,5))
        tk.Label(form, text="Periods/Week").grid(row=10, column=0, sticky="w"); self.course_periods_var = tk.IntVar(value=2); tk.Spinbox(form, from_=1, to=10, textvariable=self.course_periods_var, width=10).grid(row=11, column=0, sticky='w')
        tk.Label(form, text="Consecutive").grid(row=10, column=1, sticky="w"); self.course_consecutive_var = tk.IntVar(value=2); tk.Spinbox(form, from_=1, to=5, textvariable=self.course_consecutive_var, width=10).grid(row=11, column=1, sticky='w')
        self.course_dependency_var = tk.BooleanVar(); tk.Checkbutton(form, text="Lab must be after Lec", variable=self.course_dependency_var).grid(row=12, column=0, columnspan=2, sticky='w', pady=5)
    
    def on_inst_select(self, _=None):
        if not self.inst_tree.selection(): return
        data = self.instructors[self.inst_tree.index(self.inst_tree.selection()[0])]
        self.inst_name_var.set(data['name']); self.inst_pref_var.set(data['preferred'])
        for (d,t), var in self.inst_unav_vars.items(): var.set(f"{d} {t}" in data['unavailable_times'])
    
    def add_update_instructor(self):
        name = self.inst_name_var.get().strip()
        if not name: return messagebox.showwarning("Input Error", "Instructor name cannot be empty.")
        times = sorted([f"{d} {t}" for (d,t), v in self.inst_unav_vars.items() if v.get()])
        data = {'name': name, 'preferred': self.inst_pref_var.get(), 'unavailable_times': times}
        sel = self.inst_tree.selection()
        if sel: self.instructors[self.inst_tree.index(sel[0])] = data
        else:
            if any(i['name'] == name for i in self.instructors): return messagebox.showwarning("Duplicate", f"Instructor '{name}' already exists.")
            self.instructors.append(data)
        self.refresh_inst_tree(); self.clear_inst_form(); self.update_course_instructor_options()
    
    def delete_instructor(self):
        if not self.inst_tree.selection(): return
        self.instructors.pop(self.inst_tree.index(self.inst_tree.selection()[0]))
        self.refresh_inst_tree(); self.clear_inst_form(); self.update_course_instructor_options()
    
    def clear_inst_form(self):
        self.inst_name_var.set(''); self.inst_pref_var.set(''); self.inst_tree.selection_remove(self.inst_tree.selection())
        for v in self.inst_unav_vars.values(): v.set(False)
    
    def refresh_inst_tree(self):
        self.inst_tree.delete(*self.inst_tree.get_children())
        for item in self.instructors: self.inst_tree.insert('', 'end', values=(item['name'], item['preferred'], len(item['unavailable_times'])))
    
    def on_room_select(self, _=None):
        if not self.room_tree.selection(): return
        data = self.rooms[self.room_tree.index(self.room_tree.selection()[0])]
        self.room_name_var.set(data['name']); self.room_cap_var.set(data['capacity']); self.room_type_var.set(data['room_type'])
        for (d,t), var in self.room_unav_vars.items(): var.set(f"{d} {t}" in data.get('unavailable_times', []))

    def add_update_room(self):
        name = self.room_name_var.get().strip()
        if not name: return messagebox.showwarning("Input Error", "Room name cannot be empty.")
        times = sorted([f"{d} {t}" for (d,t), v in self.room_unav_vars.items() if v.get()])
        data = {'name': name, 'capacity': self.room_cap_var.get(), 'room_type': self.room_type_var.get(), 'unavailable_times': times}
        sel = self.room_tree.selection()
        if sel: self.rooms[self.room_tree.index(sel[0])] = data
        else:
            if any(r['name'] == name for r in self.rooms): return messagebox.showwarning("Duplicate", f"Room '{name}' already exists.")
            self.rooms.append(data)
        self.refresh_room_tree(); self.clear_room_form()

    def delete_room(self):
        if not self.room_tree.selection(): return
        self.rooms.pop(self.room_tree.index(self.room_tree.selection()[0])); self.refresh_room_tree(); self.clear_room_form()
    
    def clear_room_form(self):
        self.room_name_var.set(''); self.room_cap_var.set(30); self.room_type_var.set('lecture'); self.room_tree.selection_remove(self.room_tree.selection())
        for v in self.room_unav_vars.values(): v.set(False)

    def refresh_room_tree(self):
        self.room_tree.delete(*self.room_tree.get_children())
        for item in self.rooms: self.room_tree.insert('', 'end', values=(item['name'], item['capacity'], item['room_type'], len(item.get('unavailable_times', []))))
    
    def on_course_select(self, _=None):
        if not self.course_tree.selection(): return
        data = self.courses[self.course_tree.index(self.course_tree.selection()[0])]
        self.course_id_var.set(data['id']); self.course_name_var.set(data['name']); self.course_inst_var.set(data['instructor_name'])
        self.course_cohort_var.set(", ".join(data['cohort_ids'])); self.course_stud_var.set(data['students']); self.course_type_var.set(data['course_type'])
        self.course_periods_var.set(data['periods_per_week']); self.course_consecutive_var.set(data['requires_consecutive'])
        self.course_dependency_var.set(data.get('lab_must_be_after_lec', False))
    
    def add_update_course(self):
        cid, inst_name = self.course_id_var.get().strip(), self.course_inst_var.get()
        if not cid or not inst_name: return messagebox.showwarning("Input Error", "Course ID and Instructor are required.")
        if '_' not in cid: return messagebox.showwarning("Input Error", f"Course ID '{cid}' must have a suffix, e.g., _Lec or _Lab")
        if inst_name not in [i['name'] for i in self.instructors]: return messagebox.showwarning("Input Error", f"Instructor '{inst_name}' does not exist.")
        cohorts_str = self.course_cohort_var.get().strip()
        if not cohorts_str: return messagebox.showwarning("Input Error", "Cohort ID(s) cannot be empty.")
        
        cohort_ids = [c.strip() for c in cohorts_str.split(',') if c.strip()]
        
        data = {
            'id': cid, 'name': self.course_name_var.get(), 'instructor_name': inst_name,
            'cohort_ids': cohort_ids, 'students': self.course_stud_var.get(), 
            'course_type': self.course_type_var.get(), 'periods_per_week': self.course_periods_var.get(), 
            'requires_consecutive': self.course_consecutive_var.get(),
            'lab_must_be_after_lec': self.course_dependency_var.get()
        }
        sel = self.course_tree.selection()
        if sel: self.courses[self.course_tree.index(sel[0])] = data
        else:
            if any(c['id'] == cid for c in self.courses): return messagebox.showwarning("Duplicate", f"Course ID '{cid}' already exists.")
            self.courses.append(data)
        self.refresh_course_tree(); self.clear_course_form()
    
    def delete_course(self):
        if not self.course_tree.selection(): return
        self.courses.pop(self.course_tree.index(self.course_tree.selection()[0])); self.refresh_course_tree(); self.clear_course_form()
    
    def clear_course_form(self):
        self.course_id_var.set(''); self.course_name_var.set(''); self.course_inst_var.set('')
        self.course_cohort_var.set(''); self.course_stud_var.set(30)
        self.course_type_var.set('lecture'); self.course_periods_var.set(2); self.course_consecutive_var.set(2)
        self.course_dependency_var.set(False)
        self.course_tree.selection_remove(self.course_tree.selection())
    
    def refresh_course_tree(self):
        self.course_tree.delete(*self.course_tree.get_children())
        for c in self.courses: 
            self.course_tree.insert('', 'end', values=(c['id'], c['name'], c['instructor_name'], ", ".join(c['cohort_ids']), 
                                                       c['course_type'], c['students'], c['periods_per_week'], c['requires_consecutive']))
    
    def update_course_instructor_options(self):
        self.inst_combo["values"] = [x["name"] for x in self.instructors]
    
    def load_sample(self):
        courses, instructors, rooms = create_easy_data()
        self.instructors = [{'name': i.name, 'preferred': i.preferred, 'unavailable_times': list(i.unavailable_times)} for i in instructors]
        self.rooms = [{'name': r.name, 'capacity': r.capacity, 'room_type': r.room_type, 'unavailable_times': list(r.unavailable_times)} for r in rooms]
        self.courses = [c.__dict__ for c in courses]
        self.refresh_all_tables()
        messagebox.showinfo("Success", "Sample data loaded successfully.")

    def refresh_all_tables(self):
        self.refresh_inst_tree(); self.refresh_room_tree(); self.refresh_course_tree(); self.update_course_instructor_options()
        self.clear_inst_form(); self.clear_room_form(); self.clear_course_form()

    def to_dataclasses(self):
        course_objects = [Course(**c) for c in self.courses]
        instructor_objects = [Instructor(name=i['name'], unavailable_times=i['unavailable_times'], preferred=i['preferred']) for i in self.instructors]
        room_objects = [Room(name=r['name'], capacity=r['capacity'], room_type=r['room_type'], unavailable_times=r['unavailable_times']) for r in self.rooms]
        return course_objects, instructor_objects, room_objects

    def on_generate(self):
        if not self.courses: return messagebox.showwarning("No Data", "Please add courses before generating a schedule.")
        self._cancel_flag.clear()
        self.generate_btn.config(state="disabled", text="Working...")
        self.cancel_btn.config(state="normal")
        self.busy_win = tk.Toplevel(self); self.busy_win.title("Processing..."); tk.Label(self.busy_win, text="GA is evolving... Please wait.\nThis window will close automatically.").pack(padx=30, pady=20)
        self.busy_win.grab_set()
        threading.Thread(target=self._run_ga_in_thread, daemon=True).start()
        self.after(100, self._check_ga_result)

    def _run_ga_in_thread(self):
        try:
            courses, instructors, rooms = self.to_dataclasses()
            ga = EasyTimetableGA(courses, instructors, rooms)
            seed_str = self.seed_var.get().strip()
            seed = int(seed_str) if seed_str.isdigit() or (seed_str.startswith('-') and seed_str[1:].isdigit()) else None
            best_schedule = ga.evolve(
                population_size=self.pop_var.get(), generations=self.gen_var.get(),
                mutate_rate=self.mut_var.get(), patience=self.patience_var.get(),
                seed=seed, cancel_flag=self._cancel_flag)
            self.queue.put((ga, best_schedule))
        except Exception as e:
            self.queue.put(e)

    def _check_ga_result(self):
        try:
            result = self.queue.get_nowait()
            if hasattr(self, 'busy_win') and self.busy_win.winfo_exists(): self.busy_win.destroy()
            self.generate_btn.config(state="normal", text="🚀 Generate"); self.cancel_btn.config(state="disabled")
            if isinstance(result, Exception):
                messagebox.showerror("Error", f"An error occurred:\n{result}")
            else:
                ga, schedule = result
                if not self._cancel_flag.is_set():
                    ga.show_grid(self, schedule)
        except queue.Empty:
            self.after(100, self._check_ga_result)

def main():
    root = tk.Tk(); root.withdraw()
    app = DataEntryUI(root, days=['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday'], times=['08:00', '09:00', '10:00', '11:00', '13:00', '14:00', '15:00', '16:00'])
    app.protocol("WM_DELETE_WINDOW", root.destroy)
    root.mainloop()

if __name__ == "__main__":
    main()