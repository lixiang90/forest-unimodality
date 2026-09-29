import ForestUnimodality.Stage59KernelData.Cell189.Parameters
import ForestUnimodality.FiniteKernelSupportedDegree

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree000
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (0)
  centralHi := (0)
  directionLo := (0)
  directionHi := (0)

def shifts : List ℤ := [-16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 0 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 0 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 0 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 0 j q := by
  apply row.supportedDegreeCheck_sound interval witness 0 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree000

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree001
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (0)
  centralHi := (0)
  directionLo := (0)
  directionHi := (0)

def shifts : List ℤ := [-16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 1 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 1 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 1 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 1 j q := by
  apply row.supportedDegreeCheck_sound interval witness 1 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree001

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree002
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (0)
  centralHi := (0)
  directionLo := (62369461036137755087823263313 / 125000000000000000000000000000)
  directionHi := (99791137657820408140517221301 / 200000000000000000000000000000)

def shifts : List ℤ := [-16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 2 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 2 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 2 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 2 j q := by
  apply row.supportedDegreeCheck_sound interval witness 2 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree002

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree003
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (62369461036137755087823263313 / 125000000000000000000000000000)
  centralHi := (99791137657820408140517221301 / 200000000000000000000000000000)
  directionLo := (352814950700825289817787996613 / 500000000000000000000000000000)
  directionHi := (705629901401650579635575993227 / 1000000000000000000000000000000)

def shifts : List ℤ := [-16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 3 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 3 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 3 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 3 j q := by
  apply row.supportedDegreeCheck_sound interval witness 3 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree003

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree004
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (352814950700825289817787996613 / 500000000000000000000000000000)
  centralHi := (705629901401650579635575993227 / 1000000000000000000000000000000)
  directionLo := (172843320568444840089657927087 / 200000000000000000000000000000)
  directionHi := (216054150710556050112072408859 / 250000000000000000000000000000)

def shifts : List ℤ := [-16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 4 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 4 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 4 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 4 j q := by
  apply row.supportedDegreeCheck_sound interval witness 4 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree004

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree005
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (172843320568444840089657927087 / 200000000000000000000000000000)
  centralHi := (216054150710556050112072408859 / 250000000000000000000000000000)
  directionLo := (997911376578204081405172213009 / 1000000000000000000000000000000)
  directionHi := (99791137657820408140517221301 / 100000000000000000000000000000)

def shifts : List ℤ := [-16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 5 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 5 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 5 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 5 j q := by
  apply row.supportedDegreeCheck_sound interval witness 5 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree005

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree006
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (997911376578204081405172213009 / 1000000000000000000000000000000)
  centralHi := (99791137657820408140517221301 / 100000000000000000000000000000)
  directionLo := (1115698836774627903272043972387 / 1000000000000000000000000000000)
  directionHi := (278924709193656975818010993097 / 250000000000000000000000000000)

def shifts : List ℤ := [-16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 6 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 6 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 6 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 6 j q := by
  apply row.supportedDegreeCheck_sound interval witness 6 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree006

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree007
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1115698836774627903272043972387 / 1000000000000000000000000000000)
  centralHi := (278924709193656975818010993097 / 250000000000000000000000000000)
  directionLo := (1222186840567476146131226962403 / 1000000000000000000000000000000)
  directionHi := (305546710141869036532806740601 / 250000000000000000000000000000)

def shifts : List ℤ := [-16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 7 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 7 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 7 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 7 j q := by
  apply row.supportedDegreeCheck_sound interval witness 7 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree007

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree008
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1222186840567476146131226962403 / 1000000000000000000000000000000)
  centralHi := (305546710141869036532806740601 / 250000000000000000000000000000)
  directionLo := (165014083306753364217796972171 / 125000000000000000000000000000)
  directionHi := (1320112666454026913742375777369 / 1000000000000000000000000000000)

def shifts : List ℤ := [-16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 8 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 8 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 8 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 8 j q := by
  apply row.supportedDegreeCheck_sound interval witness 8 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree008

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree009
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (165014083306753364217796972171 / 125000000000000000000000000000)
  centralHi := (1320112666454026913742375777369 / 1000000000000000000000000000000)
  directionLo := (352814950700825289817787996613 / 250000000000000000000000000000)
  directionHi := (1411259802803301159271151986453 / 1000000000000000000000000000000)

def shifts : List ℤ := [-16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 9 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 9 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 9 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 9 j q := by
  apply row.supportedDegreeCheck_sound interval witness 9 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree009

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree010
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (352814950700825289817787996613 / 250000000000000000000000000000)
  centralHi := (1411259802803301159271151986453 / 1000000000000000000000000000000)
  directionLo := (748433532433653061053879159757 / 500000000000000000000000000000)
  directionHi := (299373412973461224421551663903 / 200000000000000000000000000000)

def shifts : List ℤ := [-16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 10 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 10 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 10 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 10 j q := by
  apply row.supportedDegreeCheck_sound interval witness 10 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree010

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree011
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (748433532433653061053879159757 / 500000000000000000000000000000)
  centralHi := (299373412973461224421551663903 / 200000000000000000000000000000)
  directionLo := (78891821324528241513268295051 / 50000000000000000000000000000)
  directionHi := (1577836426490564830265365901021 / 1000000000000000000000000000000)

def shifts : List ℤ := [-16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 11 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 11 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 11 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 11 j q := by
  apply row.supportedDegreeCheck_sound interval witness 11 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree011

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree012
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (78891821324528241513268295051 / 50000000000000000000000000000)
  centralHi := (1577836426490564830265365901021 / 1000000000000000000000000000000)
  directionLo := (1654848805068477291366770374287 / 1000000000000000000000000000000)
  directionHi := (103428050316779830710423148393 / 62500000000000000000000000000)

def shifts : List ℤ := [-16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 12 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 12 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 12 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 12 j q := by
  apply row.supportedDegreeCheck_sound interval witness 12 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree012

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree013
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1654848805068477291366770374287 / 1000000000000000000000000000000)
  centralHi := (103428050316779830710423148393 / 62500000000000000000000000000)
  directionLo := (1728433205684448400896579270871 / 1000000000000000000000000000000)
  directionHi := (216054150710556050112072408859 / 125000000000000000000000000000)

def shifts : List ℤ := [-16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 13 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 13 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 13 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 13 j q := by
  apply row.supportedDegreeCheck_sound interval witness 13 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree013

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree014
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1728433205684448400896579270871 / 1000000000000000000000000000000)
  centralHi := (216054150710556050112072408859 / 125000000000000000000000000000)
  directionLo := (359802063662156905713477239429 / 200000000000000000000000000000)
  directionHi := (899505159155392264283693098573 / 500000000000000000000000000000)

def shifts : List ℤ := [-16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 14 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 14 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 14 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 14 j q := by
  apply row.supportedDegreeCheck_sound interval witness 14 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree014

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree015
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (359802063662156905713477239429 / 200000000000000000000000000000)
  centralHi := (899505159155392264283693098573 / 500000000000000000000000000000)
  directionLo := (1866921236759794810641864599013 / 1000000000000000000000000000000)
  directionHi := (933460618379897405320932299507 / 500000000000000000000000000000)

def shifts : List ℤ := [-16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 15 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 15 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 15 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 15 j q := by
  apply row.supportedDegreeCheck_sound interval witness 15 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree015

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree016
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1866921236759794810641864599013 / 1000000000000000000000000000000)
  centralHi := (933460618379897405320932299507 / 500000000000000000000000000000)
  directionLo := (241555883904893908955391518161 / 125000000000000000000000000000)
  directionHi := (1932447071239151271643132145289 / 1000000000000000000000000000000)

def shifts : List ℤ := [-16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 16 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 16 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 16 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 16 j q := by
  apply row.supportedDegreeCheck_sound interval witness 16 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree016

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree017
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (241555883904893908955391518161 / 125000000000000000000000000000)
  centralHi := (1932447071239151271643132145289 / 1000000000000000000000000000000)
  directionLo := (1995822753156408162810344426019 / 1000000000000000000000000000000)
  directionHi := (99791137657820408140517221301 / 50000000000000000000000000000)

def shifts : List ℤ := [-16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 17 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 17 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 17 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 17 j q := by
  apply row.supportedDegreeCheck_sound interval witness 17 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree017

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree018
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1995822753156408162810344426019 / 1000000000000000000000000000000)
  centralHi := (99791137657820408140517221301 / 50000000000000000000000000000)
  directionLo := (2057247005318728494984978485009 / 1000000000000000000000000000000)
  directionHi := (205724700531872849498497848501 / 100000000000000000000000000000)

def shifts : List ℤ := [-16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 18 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 18 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 18 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 18 j q := by
  apply row.supportedDegreeCheck_sound interval witness 18 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree018

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree019
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (2057247005318728494984978485009 / 1000000000000000000000000000000)
  centralHi := (205724700531872849498497848501 / 100000000000000000000000000000)
  directionLo := (1058444852102475869453363989839 / 500000000000000000000000000000)
  directionHi := (2116889704204951738906727979679 / 1000000000000000000000000000000)

def shifts : List ℤ := [-16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 19 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 19 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 19 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 19 j q := by
  apply row.supportedDegreeCheck_sound interval witness 19 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree019

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree020
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1058444852102475869453363989839 / 500000000000000000000000000000)
  centralHi := (2116889704204951738906727979679 / 1000000000000000000000000000000)
  directionLo := (543724355639244127008440667279 / 250000000000000000000000000000)
  directionHi := (2174897422556976508033762669117 / 1000000000000000000000000000000)

def shifts : List ℤ := [-16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 20 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 20 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 20 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 20 j q := by
  apply row.supportedDegreeCheck_sound interval witness 20 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree020

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree021
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (543724355639244127008440667279 / 250000000000000000000000000000)
  centralHi := (2174897422556976508033762669117 / 1000000000000000000000000000000)
  directionLo := (89255906941970232261763517791 / 40000000000000000000000000000)
  directionHi := (278924709193656975818010993097 / 125000000000000000000000000000)

def shifts : List ℤ := [-16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 21 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 21 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 21 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 21 j q := by
  apply row.supportedDegreeCheck_sound interval witness 21 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree021

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree022
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (89255906941970232261763517791 / 40000000000000000000000000000)
  centralHi := (278924709193656975818010993097 / 125000000000000000000000000000)
  directionLo := (2286502210013601265190868691223 / 1000000000000000000000000000000)
  directionHi := (285812776251700158148858586403 / 125000000000000000000000000000)

def shifts : List ℤ := [-16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 22 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 22 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 22 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 22 j q := by
  apply row.supportedDegreeCheck_sound interval witness 22 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree022

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree023
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (2286502210013601265190868691223 / 1000000000000000000000000000000)
  centralHi := (285812776251700158148858586403 / 125000000000000000000000000000)
  directionLo := (2340309623804750819826351985061 / 1000000000000000000000000000000)
  directionHi := (1170154811902375409913175992531 / 500000000000000000000000000000)

def shifts : List ℤ := [-16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 23 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 23 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 23 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 23 j q := by
  apply row.supportedDegreeCheck_sound interval witness 23 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree023

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree024
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (2340309623804750819826351985061 / 1000000000000000000000000000000)
  centralHi := (1170154811902375409913175992531 / 500000000000000000000000000000)
  directionLo := (1196453709316535349142146851591 / 500000000000000000000000000000)
  directionHi := (2392907418633070698284293703183 / 1000000000000000000000000000000)

def shifts : List ℤ := [-16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 24 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 24 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 24 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 24 j q := by
  apply row.supportedDegreeCheck_sound interval witness 24 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree024

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree025
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1196453709316535349142146851591 / 500000000000000000000000000000)
  centralHi := (2392907418633070698284293703183 / 1000000000000000000000000000000)
  directionLo := (2444373681134952292262453924807 / 1000000000000000000000000000000)
  directionHi := (305546710141869036532806740601 / 125000000000000000000000000000)

def shifts : List ℤ := [-16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 25 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 25 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 25 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 25 j q := by
  apply row.supportedDegreeCheck_sound interval witness 25 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree025

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree026
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (2444373681134952292262453924807 / 1000000000000000000000000000000)
  centralHi := (305546710141869036532806740601 / 125000000000000000000000000000)
  directionLo := (2494778441445510203512930532523 / 1000000000000000000000000000000)
  directionHi := (623694610361377550878232633131 / 250000000000000000000000000000)

def shifts : List ℤ := [-16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 26 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 26 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 26 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 26 j q := by
  apply row.supportedDegreeCheck_sound interval witness 26 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree026

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree027
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (2494778441445510203512930532523 / 1000000000000000000000000000000)
  centralHi := (623694610361377550878232633131 / 250000000000000000000000000000)
  directionLo := (318023098875531281708084713803 / 125000000000000000000000000000)
  directionHi := (101767391640170010146587108417 / 40000000000000000000000000000)

def shifts : List ℤ := [-16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 27 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 27 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 27 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 27 j q := by
  apply row.supportedDegreeCheck_sound interval witness 27 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree027

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree028
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (318023098875531281708084713803 / 125000000000000000000000000000)
  centralHi := (101767391640170010146587108417 / 40000000000000000000000000000)
  directionLo := (2592649808526672601344868906307 / 1000000000000000000000000000000)
  directionHi := (648162452131668150336217226577 / 250000000000000000000000000000)

def shifts : List ℤ := [-16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 28 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 28 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 28 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 28 j q := by
  apply row.supportedDegreeCheck_sound interval witness 28 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree028

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree029
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (2592649808526672601344868906307 / 1000000000000000000000000000000)
  centralHi := (648162452131668150336217226577 / 250000000000000000000000000000)
  directionLo := (165014083306753364217796972171 / 62500000000000000000000000000)
  directionHi := (2640225332908053827484751554737 / 1000000000000000000000000000000)

def shifts : List ℤ := [-16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 29 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 29 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 29 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 29 j q := by
  apply row.supportedDegreeCheck_sound interval witness 29 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree029

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree030
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (165014083306753364217796972171 / 62500000000000000000000000000)
  centralHi := (2640225332908053827484751554737 / 1000000000000000000000000000000)
  directionLo := (2686958612894045902713805398349 / 1000000000000000000000000000000)
  directionHi := (53739172257880918054276107967 / 20000000000000000000000000000)

def shifts : List ℤ := [-16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 30 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 30 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 30 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 30 j q := by
  apply row.supportedDegreeCheck_sound interval witness 30 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree030

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree031
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (2686958612894045902713805398349 / 1000000000000000000000000000000)
  centralHi := (53739172257880918054276107967 / 20000000000000000000000000000)
  directionLo := (1366446428357287154038957547171 / 500000000000000000000000000000)
  directionHi := (2732892856714574308077915094343 / 1000000000000000000000000000000)

def shifts : List ℤ := [-16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 31 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 31 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 31 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 31 j q := by
  apply row.supportedDegreeCheck_sound interval witness 31 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree031

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree032
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1366446428357287154038957547171 / 500000000000000000000000000000)
  centralHi := (2732892856714574308077915094343 / 1000000000000000000000000000000)
  directionLo := (1389033849943693627325748308347 / 500000000000000000000000000000)
  directionHi := (555613539977477450930299323339 / 200000000000000000000000000000)

def shifts : List ℤ := [-16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 32 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 32 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 32 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 32 j q := by
  apply row.supportedDegreeCheck_sound interval witness 32 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree032

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree033
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1389033849943693627325748308347 / 500000000000000000000000000000)
  centralHi := (555613539977477450930299323339 / 200000000000000000000000000000)
  directionLo := (564503921121320463708460794581 / 200000000000000000000000000000)
  directionHi := (1411259802803301159271151986453 / 500000000000000000000000000000)

def shifts : List ℤ := [-16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 33 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 33 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 33 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 33 j q := by
  apply row.supportedDegreeCheck_sound interval witness 33 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree033

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree034
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (564503921121320463708460794581 / 200000000000000000000000000000)
  centralHi := (1411259802803301159271151986453 / 500000000000000000000000000000)
  directionLo := (2866282209223247692197472748891 / 1000000000000000000000000000000)
  directionHi := (716570552305811923049368187223 / 250000000000000000000000000000)

def shifts : List ℤ := [-16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 34 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 34 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 34 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 34 j q := by
  apply row.supportedDegreeCheck_sound interval witness 34 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree034

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree035
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (2866282209223247692197472748891 / 1000000000000000000000000000000)
  centralHi := (716570552305811923049368187223 / 250000000000000000000000000000)
  directionLo := (2909386616073180642050124549991 / 1000000000000000000000000000000)
  directionHi := (363673327009147580256265568749 / 125000000000000000000000000000)

def shifts : List ℤ := [-16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 35 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 35 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 35 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 35 j q := by
  apply row.supportedDegreeCheck_sound interval witness 35 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree035

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree036
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (2909386616073180642050124549991 / 1000000000000000000000000000000)
  centralHi := (363673327009147580256265568749 / 125000000000000000000000000000)
  directionLo := (147593083007485521665421527787 / 50000000000000000000000000000)
  directionHi := (2951861660149710433308430555741 / 1000000000000000000000000000000)

def shifts : List ℤ := [-16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 36 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 36 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 36 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 36 j q := by
  apply row.supportedDegreeCheck_sound interval witness 36 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree036

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree037
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (147593083007485521665421527787 / 50000000000000000000000000000)
  centralHi := (2951861660149710433308430555741 / 1000000000000000000000000000000)
  directionLo := (748433532433653061053879159757 / 250000000000000000000000000000)
  directionHi := (2993734129734612244215516639029 / 1000000000000000000000000000000)

def shifts : List ℤ := [-16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 37 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 37 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 37 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 37 j q := by
  apply row.supportedDegreeCheck_sound interval witness 37 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree037

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree038
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (748433532433653061053879159757 / 250000000000000000000000000000)
  centralHi := (2993734129734612244215516639029 / 1000000000000000000000000000000)
  directionLo := (37937862062551351383980313097 / 12500000000000000000000000000)
  directionHi := (3035028965004108110718425047761 / 1000000000000000000000000000000)

def shifts : List ℤ := [-16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 38 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 38 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 38 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 38 j q := by
  apply row.supportedDegreeCheck_sound interval witness 38 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree038

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree039
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (37937862062551351383980313097 / 12500000000000000000000000000)
  centralHi := (3035028965004108110718425047761 / 1000000000000000000000000000000)
  directionLo := (3075769431750364355384311293529 / 1000000000000000000000000000000)
  directionHi := (307576943175036435538431129353 / 100000000000000000000000000000)

def shifts : List ℤ := [-16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 39 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 39 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 39 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 39 j q := by
  apply row.supportedDegreeCheck_sound interval witness 39 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree039

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree040
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3075769431750364355384311293529 / 1000000000000000000000000000000)
  centralHi := (307576943175036435538431129353 / 100000000000000000000000000000)
  directionLo := (97374289832966791888026395709 / 31250000000000000000000000000)
  directionHi := (3115977274654937340416844662689 / 1000000000000000000000000000000)

def shifts : List ℤ := [-16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 40 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 40 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 40 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 40 j q := by
  apply row.supportedDegreeCheck_sound interval witness 40 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree040

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree041
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (97374289832966791888026395709 / 31250000000000000000000000000)
  centralHi := (3115977274654937340416844662689 / 1000000000000000000000000000000)
  directionLo := (3155672852981129660530731802041 / 1000000000000000000000000000000)
  directionHi := (1577836426490564830265365901021 / 500000000000000000000000000000)

def shifts : List ℤ := [-15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 41 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 41 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 41 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 41 j q := by
  apply row.supportedDegreeCheck_sound interval witness 41 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree041

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree042
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3155672852981129660530731802041 / 1000000000000000000000000000000)
  centralHi := (1577836426490564830265365901021 / 500000000000000000000000000000)
  directionLo := (1597437630544469327040325999727 / 500000000000000000000000000000)
  directionHi := (638975052217787730816130399891 / 200000000000000000000000000000)

def shifts : List ℤ := [-14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 42 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 42 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 42 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 42 j q := by
  apply row.supportedDegreeCheck_sound interval witness 42 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree042

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree043
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1597437630544469327040325999727 / 500000000000000000000000000000)
  centralHi := (638975052217787730816130399891 / 200000000000000000000000000000)
  directionLo := (3233602435797289767323478706027 / 1000000000000000000000000000000)
  directionHi := (808400608949322441830869676507 / 250000000000000000000000000000)

def shifts : List ℤ := [-13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 43 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 43 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 43 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 43 j q := by
  apply row.supportedDegreeCheck_sound interval witness 43 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree043

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree044
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3233602435797289767323478706027 / 1000000000000000000000000000000)
  centralHi := (808400608949322441830869676507 / 250000000000000000000000000000)
  directionLo := (130874850092263132576970695309 / 40000000000000000000000000000)
  directionHi := (1635935626153289157212133691363 / 500000000000000000000000000000)

def shifts : List ℤ := [-12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 44 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 44 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 44 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 44 j q := by
  apply row.supportedDegreeCheck_sound interval witness 44 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree044

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree045
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (130874850092263132576970695309 / 40000000000000000000000000000)
  centralHi := (1635935626153289157212133691363 / 500000000000000000000000000000)
  directionLo := (1654848805068477291366770374287 / 500000000000000000000000000000)
  directionHi := (132387904405478183309341629943 / 40000000000000000000000000000)

def shifts : List ℤ := [-11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 45 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 45 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 45 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 45 j q := by
  apply row.supportedDegreeCheck_sound interval witness 45 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree045

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree046
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1654848805068477291366770374287 / 500000000000000000000000000000)
  centralHi := (132387904405478183309341629943 / 40000000000000000000000000000)
  directionLo := (3347096510323883709816131917163 / 1000000000000000000000000000000)
  directionHi := (836774127580970927454032979291 / 250000000000000000000000000000)

def shifts : List ℤ := [-10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 46 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 46 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 46 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 46 j q := by
  apply row.supportedDegreeCheck_sound interval witness 46 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree046

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree047
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3347096510323883709816131917163 / 1000000000000000000000000000000)
  centralHi := (836774127580970927454032979291 / 250000000000000000000000000000)
  directionLo := (3384082124934081993351286788791 / 1000000000000000000000000000000)
  directionHi := (423010265616760249168910848599 / 125000000000000000000000000000)

def shifts : List ℤ := [-9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 47 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 47 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 47 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 47 j q := by
  apply row.supportedDegreeCheck_sound interval witness 47 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree047

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree048
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3384082124934081993351286788791 / 1000000000000000000000000000000)
  centralHi := (423010265616760249168910848599 / 125000000000000000000000000000)
  directionLo := (855166964953862945650937510661 / 250000000000000000000000000000)
  directionHi := (684133571963090356520750008529 / 200000000000000000000000000000)

def shifts : List ℤ := [-8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 48 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 48 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 48 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 48 j q := by
  apply row.supportedDegreeCheck_sound interval witness 48 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree048

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree049
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (855166964953862945650937510661 / 250000000000000000000000000000)
  centralHi := (684133571963090356520750008529 / 200000000000000000000000000000)
  directionLo := (3456866411368896801793158541743 / 1000000000000000000000000000000)
  directionHi := (216054150710556050112072408859 / 62500000000000000000000000000)

def shifts : List ℤ := [-7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 49 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 49 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 49 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 49 j q := by
  apply row.supportedDegreeCheck_sound interval witness 49 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree049

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree050
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3456866411368896801793158541743 / 1000000000000000000000000000000)
  centralHi := (216054150710556050112072408859 / 62500000000000000000000000000)
  directionLo := (3492689818023714284918102745533 / 1000000000000000000000000000000)
  directionHi := (1746344909011857142459051372767 / 500000000000000000000000000000)

def shifts : List ℤ := [-6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 50 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 50 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 50 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 50 j q := by
  apply row.supportedDegreeCheck_sound interval witness 50 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree050

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree051
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3492689818023714284918102745533 / 1000000000000000000000000000000)
  centralHi := (1746344909011857142459051372767 / 500000000000000000000000000000)
  directionLo := (3528149507008252898177879966131 / 1000000000000000000000000000000)
  directionHi := (882037376752063224544469991533 / 250000000000000000000000000000)

def shifts : List ℤ := [-5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 51 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 51 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 51 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 51 j q := by
  apply row.supportedDegreeCheck_sound interval witness 51 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree051

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree052
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3528149507008252898177879966131 / 1000000000000000000000000000000)
  centralHi := (882037376752063224544469991533 / 250000000000000000000000000000)
  directionLo := (712651267386191618091157942559 / 200000000000000000000000000000)
  directionHi := (890814084232739522613947428199 / 250000000000000000000000000000)

def shifts : List ℤ := [-4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 52 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 52 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 52 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 52 j q := by
  apply row.supportedDegreeCheck_sound interval witness 52 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree052

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree053
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (712651267386191618091157942559 / 200000000000000000000000000000)
  centralHi := (890814084232739522613947428199 / 250000000000000000000000000000)
  directionLo := (359802063662156905713477239429 / 100000000000000000000000000000)
  directionHi := (3598020636621569057134772394291 / 1000000000000000000000000000000)

def shifts : List ℤ := [-3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 53 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 53 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 53 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 53 j q := by
  apply row.supportedDegreeCheck_sound interval witness 53 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree053

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree054
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (359802063662156905713477239429 / 100000000000000000000000000000)
  centralHi := (3598020636621569057134772394291 / 1000000000000000000000000000000)
  directionLo := (454056530078282430560250138259 / 125000000000000000000000000000)
  directionHi := (3632452240626259444482001106073 / 1000000000000000000000000000000)

def shifts : List ℤ := [-2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 54 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 54 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 54 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 54 j q := by
  apply row.supportedDegreeCheck_sound interval witness 54 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree054

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree055
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (454056530078282430560250138259 / 125000000000000000000000000000)
  centralHi := (3632452240626259444482001106073 / 1000000000000000000000000000000)
  directionLo := (3666560521702428438393680887211 / 1000000000000000000000000000000)
  directionHi := (916640130425607109598420221803 / 250000000000000000000000000000)

def shifts : List ℤ := [-1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 55 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 55 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 55 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 55 j q := by
  apply row.supportedDegreeCheck_sound interval witness 55 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree055

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree056
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3666560521702428438393680887211 / 1000000000000000000000000000000)
  centralHi := (916640130425607109598420221803 / 250000000000000000000000000000)
  directionLo := (462544302577176718158148984657 / 125000000000000000000000000000)
  directionHi := (3700354420617413745265191877257 / 1000000000000000000000000000000)

def shifts : List ℤ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 56 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 56 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 56 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 56 j q := by
  apply row.supportedDegreeCheck_sound interval witness 56 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree056

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree057
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (462544302577176718158148984657 / 125000000000000000000000000000)
  centralHi := (3700354420617413745265191877257 / 1000000000000000000000000000000)
  directionLo := (1866921236759794810641864599013 / 500000000000000000000000000000)
  directionHi := (3733842473519589621283729198027 / 1000000000000000000000000000000)

def shifts : List ℤ := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 57 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 57 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 57 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 57 j q := by
  apply row.supportedDegreeCheck_sound interval witness 57 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree057

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree058
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1866921236759794810641864599013 / 500000000000000000000000000000)
  centralHi := (3733842473519589621283729198027 / 1000000000000000000000000000000)
  directionLo := (1883516418559640461831976118561 / 500000000000000000000000000000)
  directionHi := (3767032837119280923663952237123 / 1000000000000000000000000000000)

def shifts : List ℤ := [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 58 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 58 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 58 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 58 j q := by
  apply row.supportedDegreeCheck_sound interval witness 58 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree058

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree059
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1883516418559640461831976118561 / 500000000000000000000000000000)
  centralHi := (3767032837119280923663952237123 / 1000000000000000000000000000000)
  directionLo := (237495831993122421217138631021 / 62500000000000000000000000000)
  directionHi := (3799933311889958739474218096337 / 1000000000000000000000000000000)

def shifts : List ℤ := [3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 59 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 59 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 59 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 59 j q := by
  apply row.supportedDegreeCheck_sound interval witness 59 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree059

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree060
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (237495831993122421217138631021 / 62500000000000000000000000000)
  centralHi := (3799933311889958739474218096337 / 1000000000000000000000000000000)
  directionLo := (3832551363476690836586395677539 / 1000000000000000000000000000000)
  directionHi := (191627568173834541829319783877 / 50000000000000000000000000000)

def shifts : List ℤ := [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 60 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 60 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 60 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 60 j q := by
  apply row.supportedDegreeCheck_sound interval witness 60 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree060

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree061
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3832551363476690836586395677539 / 1000000000000000000000000000000)
  centralHi := (191627568173834541829319783877 / 50000000000000000000000000000)
  directionLo := (3864894142478302543286264290577 / 1000000000000000000000000000000)
  directionHi := (1932447071239151271643132145289 / 500000000000000000000000000000)

def shifts : List ℤ := [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 61 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 61 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 61 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 61 j q := by
  apply row.supportedDegreeCheck_sound interval witness 61 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree061

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree062
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3864894142478302543286264290577 / 1000000000000000000000000000000)
  centralHi := (1932447071239151271643132145289 / 500000000000000000000000000000)
  directionLo := (3896968502751740886702544514413 / 1000000000000000000000000000000)
  directionHi := (1948484251375870443351272257207 / 500000000000000000000000000000)

def shifts : List ℤ := [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 62 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 62 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 62 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 62 j q := by
  apply row.supportedDegreeCheck_sound interval witness 62 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree062

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree063
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3896968502751740886702544514413 / 1000000000000000000000000000000)
  centralHi := (1948484251375870443351272257207 / 500000000000000000000000000000)
  directionLo := (1964390509185686116168986995693 / 500000000000000000000000000000)
  directionHi := (3928781018371372232337973991387 / 1000000000000000000000000000000)

def shifts : List ℤ := [7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 63 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 63 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 63 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 63 j q := by
  apply row.supportedDegreeCheck_sound interval witness 63 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree063

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree064
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1964390509185686116168986995693 / 500000000000000000000000000000)
  centralHi := (3928781018371372232337973991387 / 1000000000000000000000000000000)
  directionLo := (495042249920260092653390916513 / 125000000000000000000000000000)
  directionHi := (792067599872416148245425466421 / 200000000000000000000000000000)

def shifts : List ℤ := [8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 64 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 64 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 64 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 64 j q := by
  apply row.supportedDegreeCheck_sound interval witness 64 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree064

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree065
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (495042249920260092653390916513 / 125000000000000000000000000000)
  centralHi := (792067599872416148245425466421 / 200000000000000000000000000000)
  directionLo := (1995822753156408162810344426019 / 500000000000000000000000000000)
  directionHi := (3991645506312816325620688852039 / 1000000000000000000000000000000)

def shifts : List ℤ := [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 65 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 65 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 65 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 65 j q := by
  apply row.supportedDegreeCheck_sound interval witness 65 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree065

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree066
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1995822753156408162810344426019 / 500000000000000000000000000000)
  centralHi := (3991645506312816325620688852039 / 1000000000000000000000000000000)
  directionLo := (4022709363966448838902091847111 / 1000000000000000000000000000000)
  directionHi := (502838670495806104862761480889 / 125000000000000000000000000000)

def shifts : List ℤ := [10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 66 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 66 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 66 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 66 j q := by
  apply row.supportedDegreeCheck_sound interval witness 66 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree066

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree067
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (4022709363966448838902091847111 / 1000000000000000000000000000000)
  centralHi := (502838670495806104862761480889 / 125000000000000000000000000000)
  directionLo := (202676758693611703636021365579 / 50000000000000000000000000000)
  directionHi := (4053535173872234072720427311581 / 1000000000000000000000000000000)

def shifts : List ℤ := [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 67 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 67 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 67 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 67 j q := by
  apply row.supportedDegreeCheck_sound interval witness 67 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree067

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree068
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (202676758693611703636021365579 / 50000000000000000000000000000)
  centralHi := (4053535173872234072720427311581 / 1000000000000000000000000000000)
  directionLo := (127629010193085234788210144081 / 31250000000000000000000000000)
  directionHi := (4084128326178727513222724610593 / 1000000000000000000000000000000)

def shifts : List ℤ := [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 68 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 68 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 68 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 68 j q := by
  apply row.supportedDegreeCheck_sound interval witness 68 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree068

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree069
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (127629010193085234788210144081 / 31250000000000000000000000000)
  centralHi := (4084128326178727513222724610593 / 1000000000000000000000000000000)
  directionLo := (2057247005318728494984978485009 / 500000000000000000000000000000)
  directionHi := (4114494010637456989969956970019 / 1000000000000000000000000000000)

def shifts : List ℤ := [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 69 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 69 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 69 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 69 j q := by
  apply row.supportedDegreeCheck_sound interval witness 69 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree069

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree070
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (2057247005318728494984978485009 / 500000000000000000000000000000)
  centralHi := (4114494010637456989969956970019 / 1000000000000000000000000000000)
  directionLo := (207231861344048381791254685333 / 50000000000000000000000000000)
  directionHi := (4144637226880967635825093706661 / 1000000000000000000000000000000)

def shifts : List ℤ := [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 70 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 70 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 70 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 70 j q := by
  apply row.supportedDegreeCheck_sound interval witness 70 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree070

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree071
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (207231861344048381791254685333 / 50000000000000000000000000000)
  centralHi := (4144637226880967635825093706661 / 1000000000000000000000000000000)
  directionLo := (4174562794032880415307069130533 / 1000000000000000000000000000000)
  directionHi := (2087281397016440207653534565267 / 500000000000000000000000000000)

def shifts : List ℤ := [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 71 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 71 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 71 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 71 j q := by
  apply row.supportedDegreeCheck_sound interval witness 71 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree071

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree072
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (4174562794032880415307069130533 / 1000000000000000000000000000000)
  centralHi := (2087281397016440207653534565267 / 500000000000000000000000000000)
  directionLo := (4204275359702271060573713475037 / 1000000000000000000000000000000)
  directionHi := (2102137679851135530286856737519 / 500000000000000000000000000000)

def shifts : List ℤ := [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 72 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 72 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 72 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 72 j q := by
  apply row.supportedDegreeCheck_sound interval witness 72 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree072

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree073
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (4204275359702271060573713475037 / 1000000000000000000000000000000)
  centralHi := (2102137679851135530286856737519 / 500000000000000000000000000000)
  directionLo := (4233779408409903477813455959357 / 1000000000000000000000000000000)
  directionHi := (2116889704204951738906727979679 / 500000000000000000000000000000)

def shifts : List ℤ := [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 73 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 73 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 73 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 73 j q := by
  apply row.supportedDegreeCheck_sound interval witness 73 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree073

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree074
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (4233779408409903477813455959357 / 1000000000000000000000000000000)
  centralHi := (2116889704204951738906727979679 / 500000000000000000000000000000)
  directionLo := (4263079269489574460868678820093 / 1000000000000000000000000000000)
  directionHi := (2131539634744787230434339410047 / 500000000000000000000000000000)

def shifts : List ℤ := [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 74 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 74 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 74 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 74 j q := by
  apply row.supportedDegreeCheck_sound interval witness 74 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree074

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree075
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (4263079269489574460868678820093 / 1000000000000000000000000000000)
  centralHi := (2131539634744787230434339410047 / 500000000000000000000000000000)
  directionLo := (4292179124503987355704940800483 / 1000000000000000000000000000000)
  directionHi := (1073044781125996838926235200121 / 250000000000000000000000000000)

def shifts : List ℤ := [19, 20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 75 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 75 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 75 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 75 j q := by
  apply row.supportedDegreeCheck_sound interval witness 75 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree075

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree076
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (4292179124503987355704940800483 / 1000000000000000000000000000000)
  centralHi := (1073044781125996838926235200121 / 250000000000000000000000000000)
  directionLo := (4321083014211121002241448177179 / 1000000000000000000000000000000)
  directionHi := (216054150710556050112072408859 / 50000000000000000000000000000)

def shifts : List ℤ := [20, 21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 76 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 76 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 76 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 76 j q := by
  apply row.supportedDegreeCheck_sound interval witness 76 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree076

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree077
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (4321083014211121002241448177179 / 1000000000000000000000000000000)
  centralHi := (216054150710556050112072408859 / 50000000000000000000000000000)
  directionLo := (543724355639244127008440667279 / 125000000000000000000000000000)
  directionHi := (4349794845113953016067525338233 / 1000000000000000000000000000000)

def shifts : List ℤ := [21, 22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 77 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 77 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 77 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 77 j q := by
  apply row.supportedDegreeCheck_sound interval witness 77 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree077

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree078
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (543724355639244127008440667279 / 125000000000000000000000000000)
  centralHi := (4349794845113953016067525338233 / 1000000000000000000000000000000)
  directionLo := (437831839562359489991762786877 / 100000000000000000000000000000)
  directionHi := (4378318395623594899917627868771 / 1000000000000000000000000000000)

def shifts : List ℤ := [22, 23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 78 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 78 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 78 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 78 j q := by
  apply row.supportedDegreeCheck_sound interval witness 78 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree078

namespace ForestUnimodality.Stage59KernelData.Cell189.Degree079
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (437831839562359489991762786877 / 100000000000000000000000000000)
  centralHi := (4378318395623594899917627868771 / 1000000000000000000000000000000)
  directionLo := (881331464372673390086009866333 / 200000000000000000000000000000)
  directionHi := (2203328660931683475215024665833 / 500000000000000000000000000000)

def shifts : List ℤ := [23, 24, 25, 26, 27, 28]

theorem shifts_checked : geometryShifts 79 pairs 79 = shifts := by decide +kernel

theorem checked : row.supportedDegreeCheck interval witness 79 shifts = true := by decide +kernel

theorem actual_residual_nonneg (j : ℤ)
    (hs : geometrySupportCheck pairs 79 j = true)
    {q : ℝ} (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 79 j q := by
  apply row.supportedDegreeCheck_sound interval witness 79 shifts row_checked interval_checked checked ?_ hq
  have hb : pairs.all (fun nk => decide (nk.1 ≤ 79 ∧ nk.2 ≤ 79)) = true := by decide +kernel
  have hmem := mem_geometryShifts (fun nk hn => of_decide_eq_true (List.all_eq_true.mp hb nk hn)) hs
  simpa only [shifts_checked] using hmem

#print axioms shifts_checked
#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage59KernelData.Cell189.Degree079
