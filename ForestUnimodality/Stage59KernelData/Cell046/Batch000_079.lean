import ForestUnimodality.Stage59KernelData.Cell046.Parameters
import ForestUnimodality.FiniteKernelSupportedDegree

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree000
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (0)
  centralHi := (0)
  directionLo := (0)
  directionHi := (0)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree000

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree001
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (0)
  centralHi := (0)
  directionLo := (0)
  directionHi := (0)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree001

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree002
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (0)
  centralHi := (0)
  directionLo := (499506741417230912442833994439 / 1000000000000000000000000000000)
  directionHi := (12487668535430772811070849861 / 25000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree002

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree003
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (499506741417230912442833994439 / 1000000000000000000000000000000)
  centralHi := (12487668535430772811070849861 / 25000000000000000000000000000)
  directionLo := (88301151026129818616015582777 / 125000000000000000000000000000)
  directionHi := (706409208209038548928124662217 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree003

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree004
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (88301151026129818616015582777 / 125000000000000000000000000000)
  centralHi := (706409208209038548928124662217 / 1000000000000000000000000000000)
  directionLo := (865171054857813168758105269779 / 1000000000000000000000000000000)
  directionHi := (43258552742890658437905263489 / 50000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree004

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree005
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (865171054857813168758105269779 / 1000000000000000000000000000000)
  centralHi := (43258552742890658437905263489 / 50000000000000000000000000000)
  directionLo := (499506741417230912442833994439 / 500000000000000000000000000000)
  directionHi := (999013482834461824885667988879 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree005

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree006
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (499506741417230912442833994439 / 500000000000000000000000000000)
  centralHi := (999013482834461824885667988879 / 1000000000000000000000000000000)
  directionLo := (44677241161133518479006615637 / 40000000000000000000000000000)
  directionHi := (558465514514168980987582695463 / 500000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree006

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree007
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (44677241161133518479006615637 / 40000000000000000000000000000)
  centralHi := (558465514514168980987582695463 / 500000000000000000000000000000)
  directionLo := (1223536639552556401853891486511 / 1000000000000000000000000000000)
  directionHi := (76471039972034775115868217907 / 62500000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree007

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree008
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1223536639552556401853891486511 / 1000000000000000000000000000000)
  centralHi := (76471039972034775115868217907 / 62500000000000000000000000000)
  directionLo := (1321570615990240119973031084687 / 1000000000000000000000000000000)
  directionHi := (82598163499390007498314442793 / 62500000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree008

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree009
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1321570615990240119973031084687 / 1000000000000000000000000000000)
  centralHi := (82598163499390007498314442793 / 62500000000000000000000000000)
  directionLo := (88301151026129818616015582777 / 62500000000000000000000000000)
  directionHi := (1412818416418077097856249324433 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree009

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree010
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (88301151026129818616015582777 / 62500000000000000000000000000)
  centralHi := (1412818416418077097856249324433 / 1000000000000000000000000000000)
  directionLo := (1498520224251692737328501983317 / 1000000000000000000000000000000)
  directionHi := (749260112125846368664250991659 / 500000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree010

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree011
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1498520224251692737328501983317 / 1000000000000000000000000000000)
  centralHi := (749260112125846368664250991659 / 500000000000000000000000000000)
  directionLo := (315915801897442532985633472003 / 200000000000000000000000000000)
  directionHi := (98723688092950791558010460001 / 62500000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree011

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree012
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (315915801897442532985633472003 / 200000000000000000000000000000)
  centralHi := (98723688092950791558010460001 / 62500000000000000000000000000)
  directionLo := (414169110383508099473449568217 / 250000000000000000000000000000)
  directionHi := (1656676441534032397893798272869 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree012

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree013
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (414169110383508099473449568217 / 250000000000000000000000000000)
  centralHi := (1656676441534032397893798272869 / 1000000000000000000000000000000)
  directionLo := (1730342109715626337516210539559 / 1000000000000000000000000000000)
  directionHi := (43258552742890658437905263489 / 25000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree013

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree014
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1730342109715626337516210539559 / 1000000000000000000000000000000)
  centralHi := (43258552742890658437905263489 / 25000000000000000000000000000)
  directionLo := (1800997168619758003186140089167 / 1000000000000000000000000000000)
  directionHi := (112562323038734875199133755573 / 62500000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree014

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree015
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1800997168619758003186140089167 / 1000000000000000000000000000000)
  centralHi := (112562323038734875199133755573 / 62500000000000000000000000000)
  directionLo := (1868983088767163090770124100391 / 1000000000000000000000000000000)
  directionHi := (233622886095895386346265512549 / 125000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree015

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree016
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1868983088767163090770124100391 / 1000000000000000000000000000000)
  centralHi := (233622886095895386346265512549 / 125000000000000000000000000000)
  directionLo := (120911330676704368359892939649 / 62500000000000000000000000000)
  directionHi := (386916258165453978751657406877 / 200000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree016

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree017
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (120911330676704368359892939649 / 62500000000000000000000000000)
  centralHi := (386916258165453978751657406877 / 200000000000000000000000000000)
  directionLo := (499506741417230912442833994439 / 250000000000000000000000000000)
  directionHi := (1998026965668923649771335977757 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree017

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree018
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (499506741417230912442833994439 / 250000000000000000000000000000)
  centralHi := (1998026965668923649771335977757 / 1000000000000000000000000000000)
  directionLo := (2059519055571330855560198977377 / 1000000000000000000000000000000)
  directionHi := (1029759527785665427780099488689 / 500000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree018

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree019
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (2059519055571330855560198977377 / 1000000000000000000000000000000)
  centralHi := (1029759527785665427780099488689 / 500000000000000000000000000000)
  directionLo := (264903453078389455848046748331 / 125000000000000000000000000000)
  directionHi := (2119227624627115646784373986649 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree019

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree020
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (264903453078389455848046748331 / 125000000000000000000000000000)
  centralHi := (2119227624627115646784373986649 / 1000000000000000000000000000000)
  directionLo := (544324851863753057620592124063 / 250000000000000000000000000000)
  directionHi := (2177299407455012230482368496253 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree020

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree021
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (544324851863753057620592124063 / 250000000000000000000000000000)
  centralHi := (2177299407455012230482368496253 / 1000000000000000000000000000000)
  directionLo := (2233862058056675923950330781851 / 1000000000000000000000000000000)
  directionHi := (558465514514168980987582695463 / 250000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree021

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree022
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (2233862058056675923950330781851 / 1000000000000000000000000000000)
  centralHi := (558465514514168980987582695463 / 250000000000000000000000000000)
  directionLo := (143064215792824626197062075549 / 62500000000000000000000000000)
  directionHi := (457805490537038803830598641757 / 200000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree022

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree023
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (143064215792824626197062075549 / 62500000000000000000000000000)
  centralHi := (457805490537038803830598641757 / 200000000000000000000000000000)
  directionLo := (46857885841628529589030751743 / 20000000000000000000000000000)
  directionHi := (2342894292081426479451537587151 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree023

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree024
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (46857885841628529589030751743 / 20000000000000000000000000000)
  centralHi := (2342894292081426479451537587151 / 1000000000000000000000000000000)
  directionLo := (479110035319194244892844537409 / 200000000000000000000000000000)
  directionHi := (1197775088297985612232111343523 / 500000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree024

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree025
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (479110035319194244892844537409 / 200000000000000000000000000000)
  centralHi := (1197775088297985612232111343523 / 500000000000000000000000000000)
  directionLo := (1223536639552556401853891486511 / 500000000000000000000000000000)
  directionHi := (2447073279105112803707782973023 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree025

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree026
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1223536639552556401853891486511 / 500000000000000000000000000000)
  centralHi := (2447073279105112803707782973023 / 1000000000000000000000000000000)
  directionLo := (499506741417230912442833994439 / 200000000000000000000000000000)
  directionHi := (624383426771538640553542493049 / 250000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree026

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree027
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (499506741417230912442833994439 / 200000000000000000000000000000)
  centralHi := (624383426771538640553542493049 / 250000000000000000000000000000)
  directionLo := (509398924331521143156354070579 / 200000000000000000000000000000)
  directionHi := (9949197740850022327272540441 / 3906250000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree027

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree028
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (509398924331521143156354070579 / 200000000000000000000000000000)
  centralHi := (9949197740850022327272540441 / 3906250000000000000000000000)
  directionLo := (2595513164573439506274315809339 / 1000000000000000000000000000000)
  directionHi := (129775658228671975313715790467 / 50000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree028

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree029
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (2595513164573439506274315809339 / 1000000000000000000000000000000)
  centralHi := (129775658228671975313715790467 / 50000000000000000000000000000)
  directionLo := (1321570615990240119973031084687 / 500000000000000000000000000000)
  directionHi := (4229025971168768383913699471 / 1600000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree029

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree030
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1321570615990240119973031084687 / 500000000000000000000000000000)
  centralHi := (4229025971168768383913699471 / 1600000000000000000000000000)
  directionLo := (1344963062403253441718585908723 / 500000000000000000000000000000)
  directionHi := (2689926124806506883437171817447 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree030

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree031
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1344963062403253441718585908723 / 500000000000000000000000000000)
  centralHi := (2689926124806506883437171817447 / 1000000000000000000000000000000)
  directionLo := (1367955549500586992149651450779 / 500000000000000000000000000000)
  directionHi := (2735911099001173984299302901559 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree031

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree032
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1367955549500586992149651450779 / 500000000000000000000000000000)
  centralHi := (2735911099001173984299302901559 / 1000000000000000000000000000000)
  directionLo := (2781135833856209192646717201599 / 1000000000000000000000000000000)
  directionHi := (1738209896160130745404198251 / 625000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree032

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree033
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (2781135833856209192646717201599 / 1000000000000000000000000000000)
  centralHi := (1738209896160130745404198251 / 625000000000000000000000000)
  directionLo := (565127366567230839142499729773 / 200000000000000000000000000000)
  directionHi := (1412818416418077097856249324433 / 500000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree033

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree034
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (565127366567230839142499729773 / 200000000000000000000000000000)
  centralHi := (1412818416418077097856249324433 / 500000000000000000000000000000)
  directionLo := (2869447768439354743046659444851 / 1000000000000000000000000000000)
  directionHi := (717361942109838685761664861213 / 250000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree034

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree035
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (2869447768439354743046659444851 / 1000000000000000000000000000000)
  centralHi := (717361942109838685761664861213 / 250000000000000000000000000000)
  directionLo := (182037486272175257304293128647 / 62500000000000000000000000000)
  directionHi := (2912599780354804116868690058353 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree035

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree036
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (182037486272175257304293128647 / 62500000000000000000000000000)
  centralHi := (2912599780354804116868690058353 / 1000000000000000000000000000000)
  directionLo := (591024346884089490752275931611 / 200000000000000000000000000000)
  directionHi := (369390216802555931720172457257 / 125000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree036

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree037
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (591024346884089490752275931611 / 200000000000000000000000000000)
  centralHi := (369390216802555931720172457257 / 125000000000000000000000000000)
  directionLo := (1498520224251692737328501983317 / 500000000000000000000000000000)
  directionHi := (599408089700677094931400793327 / 200000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree037

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree038
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1498520224251692737328501983317 / 500000000000000000000000000000)
  centralHi := (599408089700677094931400793327 / 200000000000000000000000000000)
  directionLo := (759595222581023508910918422171 / 250000000000000000000000000000)
  directionHi := (607676178064818807128734737737 / 200000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree038

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree039
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (759595222581023508910918422171 / 250000000000000000000000000000)
  centralHi := (607676178064818807128734737737 / 200000000000000000000000000000)
  directionLo := (1539583175684890914952175529719 / 500000000000000000000000000000)
  directionHi := (3079166351369781829904351059439 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree039

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree040
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1539583175684890914952175529719 / 500000000000000000000000000000)
  centralHi := (3079166351369781829904351059439 / 1000000000000000000000000000000)
  directionLo := (124776744013484532819930574379 / 40000000000000000000000000000)
  directionHi := (779854650084278330124566089869 / 250000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree040

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree041
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (124776744013484532819930574379 / 40000000000000000000000000000)
  centralHi := (779854650084278330124566089869 / 250000000000000000000000000000)
  directionLo := (315915801897442532985633472003 / 100000000000000000000000000000)
  directionHi := (3159158018974425329856334720031 / 1000000000000000000000000000000)

def shifts : List ℤ := [-16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree041

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree042
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (315915801897442532985633472003 / 100000000000000000000000000000)
  centralHi := (3159158018974425329856334720031 / 1000000000000000000000000000000)
  directionLo := (1599201861364886910901396712361 / 500000000000000000000000000000)
  directionHi := (3198403722729773821802793424723 / 1000000000000000000000000000000)

def shifts : List ℤ := [-15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree042

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree043
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1599201861364886910901396712361 / 500000000000000000000000000000)
  centralHi := (3198403722729773821802793424723 / 1000000000000000000000000000000)
  directionLo := (3237173668231739507655438438447 / 1000000000000000000000000000000)
  directionHi := (202323354264483719228464902403 / 62500000000000000000000000000)

def shifts : List ℤ := [-14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree043

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree044
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3237173668231739507655438438447 / 1000000000000000000000000000000)
  centralHi := (202323354264483719228464902403 / 62500000000000000000000000000)
  directionLo := (409435593664738463051824373259 / 125000000000000000000000000000)
  directionHi := (3275484749317907704414594986073 / 1000000000000000000000000000000)

def shifts : List ℤ := [-13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree044

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree045
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (409435593664738463051824373259 / 125000000000000000000000000000)
  centralHi := (3275484749317907704414594986073 / 1000000000000000000000000000000)
  directionLo := (414169110383508099473449568217 / 125000000000000000000000000000)
  directionHi := (3313352883068064795787596545737 / 1000000000000000000000000000000)

def shifts : List ℤ := [-12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree045

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree046
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (414169110383508099473449568217 / 125000000000000000000000000000)
  centralHi := (3313352883068064795787596545737 / 1000000000000000000000000000000)
  directionLo := (418849135885626735740687021597 / 125000000000000000000000000000)
  directionHi := (3350793087085013885925496172777 / 1000000000000000000000000000000)

def shifts : List ℤ := [-11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree046

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree047
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (418849135885626735740687021597 / 125000000000000000000000000000)
  centralHi := (3350793087085013885925496172777 / 1000000000000000000000000000000)
  directionLo := (3387819549087285410243017833261 / 1000000000000000000000000000000)
  directionHi := (1693909774543642705121508916631 / 500000000000000000000000000000)

def shifts : List ℤ := [-10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree047

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree048
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3387819549087285410243017833261 / 1000000000000000000000000000000)
  centralHi := (1693909774543642705121508916631 / 500000000000000000000000000000)
  directionLo := (3424445689728373868162154098717 / 1000000000000000000000000000000)
  directionHi := (1712222844864186934081077049359 / 500000000000000000000000000000)

def shifts : List ℤ := [-9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree048

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree049
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3424445689728373868162154098717 / 1000000000000000000000000000000)
  centralHi := (1712222844864186934081077049359 / 500000000000000000000000000000)
  directionLo := (1730342109715626337516210539559 / 500000000000000000000000000000)
  directionHi := (3460684219431252675032421079119 / 1000000000000000000000000000000)

def shifts : List ℤ := [-8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree049

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree050
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1730342109715626337516210539559 / 500000000000000000000000000000)
  centralHi := (3460684219431252675032421079119 / 1000000000000000000000000000000)
  directionLo := (3496547189920616387099837961073 / 1000000000000000000000000000000)
  directionHi := (1748273594960308193549918980537 / 500000000000000000000000000000)

def shifts : List ℤ := [-7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree050

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree051
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3496547189920616387099837961073 / 1000000000000000000000000000000)
  centralHi := (1748273594960308193549918980537 / 500000000000000000000000000000)
  directionLo := (3532046041045192744640623311081 / 1000000000000000000000000000000)
  directionHi := (1766023020522596372320311655541 / 500000000000000000000000000000)

def shifts : List ℤ := [-6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree051

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree052
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3532046041045192744640623311081 / 1000000000000000000000000000000)
  centralHi := (1766023020522596372320311655541 / 500000000000000000000000000000)
  directionLo := (3567191643405815080738664132489 / 1000000000000000000000000000000)
  directionHi := (356719164340581508073866413249 / 100000000000000000000000000000)

def shifts : List ℤ := [-5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree052

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree053
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3567191643405815080738664132489 / 1000000000000000000000000000000)
  centralHi := (356719164340581508073866413249 / 100000000000000000000000000000)
  directionLo := (1800997168619758003186140089167 / 500000000000000000000000000000)
  directionHi := (720398867447903201274456035667 / 200000000000000000000000000000)

def shifts : List ℤ := [-4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree053

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree054
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1800997168619758003186140089167 / 500000000000000000000000000000)
  centralHi := (720398867447903201274456035667 / 200000000000000000000000000000)
  directionLo := (1818231983976934704087688932871 / 500000000000000000000000000000)
  directionHi := (3636463967953869408175377865743 / 1000000000000000000000000000000)

def shifts : List ℤ := [-3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree054

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree055
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1818231983976934704087688932871 / 500000000000000000000000000000)
  centralHi := (3636463967953869408175377865743 / 1000000000000000000000000000000)
  directionLo := (3670609918657669205561674459533 / 1000000000000000000000000000000)
  directionHi := (1835304959328834602780837229767 / 500000000000000000000000000000)

def shifts : List ℤ := [-2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree055

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree056
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3670609918657669205561674459533 / 1000000000000000000000000000000)
  centralHi := (1835304959328834602780837229767 / 500000000000000000000000000000)
  directionLo := (3704441139992552416373368768139 / 1000000000000000000000000000000)
  directionHi := (185222056999627620818668438407 / 50000000000000000000000000000)

def shifts : List ℤ := [-1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree056

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree057
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3704441139992552416373368768139 / 1000000000000000000000000000000)
  centralHi := (185222056999627620818668438407 / 50000000000000000000000000000)
  directionLo := (3737966177534326181540248200783 / 1000000000000000000000000000000)
  directionHi := (233622886095895386346265512549 / 62500000000000000000000000000)

def shifts : List ℤ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree057

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree058
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3737966177534326181540248200783 / 1000000000000000000000000000000)
  centralHi := (233622886095895386346265512549 / 62500000000000000000000000000)
  directionLo := (942798299250422986028444084247 / 250000000000000000000000000000)
  directionHi := (3771193197001691944113776336989 / 1000000000000000000000000000000)

def shifts : List ℤ := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree058

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree059
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (942798299250422986028444084247 / 250000000000000000000000000000)
  centralHi := (3771193197001691944113776336989 / 1000000000000000000000000000000)
  directionLo := (3804130007483064779210822678759 / 1000000000000000000000000000000)
  directionHi := (95103250187076619480270566969 / 25000000000000000000000000000)

def shifts : List ℤ := [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree059

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree060
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3804130007483064779210822678759 / 1000000000000000000000000000000)
  centralHi := (95103250187076619480270566969 / 25000000000000000000000000000)
  directionLo := (3836784082868667615074285429559 / 1000000000000000000000000000000)
  directionHi := (95919602071716690376857135739 / 25000000000000000000000000000)

def shifts : List ℤ := [3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree060

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree061
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3836784082868667615074285429559 / 1000000000000000000000000000000)
  centralHi := (95919602071716690376857135739 / 25000000000000000000000000000)
  directionLo := (120911330676704368359892939649 / 31250000000000000000000000000)
  directionHi := (3869162581654539787516574068769 / 1000000000000000000000000000000)

def shifts : List ℤ := [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree061

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree062
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (120911330676704368359892939649 / 31250000000000000000000000000)
  centralHi := (3869162581654539787516574068769 / 1000000000000000000000000000000)
  directionLo := (975318091316779188827487309063 / 250000000000000000000000000000)
  directionHi := (3901272365267116755309949236253 / 1000000000000000000000000000000)

def shifts : List ℤ := [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree062

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree063
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (975318091316779188827487309063 / 250000000000000000000000000000)
  centralHi := (3901272365267116755309949236253 / 1000000000000000000000000000000)
  directionLo := (3933120015041257807806765773607 / 1000000000000000000000000000000)
  directionHi := (491640001880157225975845721701 / 125000000000000000000000000000)

def shifts : List ℤ := [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree063

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree064
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3933120015041257807806765773607 / 1000000000000000000000000000000)
  centralHi := (491640001880157225975845721701 / 125000000000000000000000000000)
  directionLo := (1982355923985360179959546627031 / 500000000000000000000000000000)
  directionHi := (3964711847970720359919093254063 / 1000000000000000000000000000000)

def shifts : List ℤ := [7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree064

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree065
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1982355923985360179959546627031 / 500000000000000000000000000000)
  centralHi := (3964711847970720359919093254063 / 1000000000000000000000000000000)
  directionLo := (499506741417230912442833994439 / 125000000000000000000000000000)
  directionHi := (3996053931337847299542671955513 / 1000000000000000000000000000000)

def shifts : List ℤ := [8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree065

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree066
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (499506741417230912442833994439 / 125000000000000000000000000000)
  centralHi := (3996053931337847299542671955513 / 1000000000000000000000000000000)
  directionLo := (4027152096318429988552242034487 / 1000000000000000000000000000000)
  directionHi := (503394012039803748569030254311 / 125000000000000000000000000000)

def shifts : List ℤ := [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree066

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree067
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (4027152096318429988552242034487 / 1000000000000000000000000000000)
  centralHi := (503394012039803748569030254311 / 125000000000000000000000000000)
  directionLo := (1014502987662036951836347212329 / 250000000000000000000000000000)
  directionHi := (4058011950648147807345388849317 / 1000000000000000000000000000000)

def shifts : List ℤ := [10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree067

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree068
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1014502987662036951836347212329 / 250000000000000000000000000000)
  centralHi := (4058011950648147807345388849317 / 1000000000000000000000000000000)
  directionLo := (4088638890428506157851945180921 / 1000000000000000000000000000000)
  directionHi := (2044319445214253078925972590461 / 500000000000000000000000000000)

def shifts : List ℤ := [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree068

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree069
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (4088638890428506157851945180921 / 1000000000000000000000000000000)
  centralHi := (2044319445214253078925972590461 / 500000000000000000000000000000)
  directionLo := (823807622228532342224079590951 / 200000000000000000000000000000)
  directionHi := (1029759527785665427780099488689 / 250000000000000000000000000000)

def shifts : List ℤ := [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree069

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree070
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (823807622228532342224079590951 / 200000000000000000000000000000)
  centralHi := (1029759527785665427780099488689 / 250000000000000000000000000000)
  directionLo := (4149214617944818573253147289143 / 1000000000000000000000000000000)
  directionHi := (518651827243102321656643411143 / 125000000000000000000000000000)

def shifts : List ℤ := [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree070

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree071
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (4149214617944818573253147289143 / 1000000000000000000000000000000)
  centralHi := (518651827243102321656643411143 / 125000000000000000000000000000)
  directionLo := (4179173235280900286936238892347 / 1000000000000000000000000000000)
  directionHi := (1044793308820225071734059723087 / 250000000000000000000000000000)

def shifts : List ℤ := [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree071

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree072
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (4179173235280900286936238892347 / 1000000000000000000000000000000)
  centralHi := (1044793308820225071734059723087 / 250000000000000000000000000000)
  directionLo := (4208918615892862276077632797981 / 1000000000000000000000000000000)
  directionHi := (2104459307946431138038816398991 / 500000000000000000000000000000)

def shifts : List ℤ := [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree072

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree073
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (4208918615892862276077632797981 / 1000000000000000000000000000000)
  centralHi := (2104459307946431138038816398991 / 500000000000000000000000000000)
  directionLo := (4238455249254231293568747973297 / 1000000000000000000000000000000)
  directionHi := (2119227624627115646784373986649 / 500000000000000000000000000000)

def shifts : List ℤ := [16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree073

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree074
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (4238455249254231293568747973297 / 1000000000000000000000000000000)
  centralHi := (2119227624627115646784373986649 / 500000000000000000000000000000)
  directionLo := (4267787469480176482403315527539 / 1000000000000000000000000000000)
  directionHi := (213389373474008824120165776377 / 50000000000000000000000000000)

def shifts : List ℤ := [17, 18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree074

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree075
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (4267787469480176482403315527539 / 1000000000000000000000000000000)
  centralHi := (213389373474008824120165776377 / 50000000000000000000000000000)
  directionLo := (4296919462751573227124181029451 / 1000000000000000000000000000000)
  directionHi := (1074229865687893306781045257363 / 250000000000000000000000000000)

def shifts : List ℤ := [18, 19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree075

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree076
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (4296919462751573227124181029451 / 1000000000000000000000000000000)
  centralHi := (1074229865687893306781045257363 / 250000000000000000000000000000)
  directionLo := (2162927637144532921895263174449 / 500000000000000000000000000000)
  directionHi := (4325855274289065843790526348899 / 1000000000000000000000000000000)

def shifts : List ℤ := [19, 20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree076

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree077
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (2162927637144532921895263174449 / 500000000000000000000000000000)
  centralHi := (4325855274289065843790526348899 / 1000000000000000000000000000000)
  directionLo := (544324851863753057620592124063 / 125000000000000000000000000000)
  directionHi := (870919762982004892192947398501 / 200000000000000000000000000000)

def shifts : List ℤ := [20, 21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree077

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree078
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (544324851863753057620592124063 / 125000000000000000000000000000)
  centralHi := (870919762982004892192947398501 / 200000000000000000000000000000)
  directionLo := (2191576933599243388736394539313 / 500000000000000000000000000000)
  directionHi := (4383153867198486777472789078627 / 1000000000000000000000000000000)

def shifts : List ℤ := [21, 22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree078

namespace ForestUnimodality.Stage59KernelData.Cell046.Degree079
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (2191576933599243388736394539313 / 500000000000000000000000000000)
  centralHi := (4383153867198486777472789078627 / 1000000000000000000000000000000)
  directionLo := (137860127853613845772036527597 / 31250000000000000000000000000)
  directionHi := (882304818263128612941033776621 / 200000000000000000000000000000)

def shifts : List ℤ := [22, 23, 24, 25]

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
end ForestUnimodality.Stage59KernelData.Cell046.Degree079
