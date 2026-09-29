import ForestUnimodality.Stage59KernelData.Cell030.Parameters
import ForestUnimodality.FiniteKernelSupportedDegree

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree000
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (0)
  centralHi := (0)
  directionLo := (0)
  directionHi := (0)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree000

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree001
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (0)
  centralHi := (0)
  directionLo := (0)
  directionHi := (0)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree001

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree002
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (0)
  centralHi := (0)
  directionLo := (15583932045641863756995628109 / 31250000000000000000000000000)
  directionHi := (498685825460539640223860099489 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree002

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree003
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (15583932045641863756995628109 / 31250000000000000000000000000)
  centralHi := (498685825460539640223860099489 / 1000000000000000000000000000000)
  directionLo := (705248257729517267430094131057 / 1000000000000000000000000000000)
  directionHi := (352624128864758633715047065529 / 500000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree003

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree004
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (705248257729517267430094131057 / 1000000000000000000000000000000)
  centralHi := (352624128864758633715047065529 / 500000000000000000000000000000)
  directionLo := (863749186712079873213718829023 / 1000000000000000000000000000000)
  directionHi := (26992162084752496037928713407 / 31250000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree004

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree005
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (863749186712079873213718829023 / 1000000000000000000000000000000)
  centralHi := (26992162084752496037928713407 / 31250000000000000000000000000)
  directionLo := (15583932045641863756995628109 / 15625000000000000000000000000)
  directionHi := (997371650921079280447720198977 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree005

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree006
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (15583932045641863756995628109 / 15625000000000000000000000000)
  centralHi := (997371650921079280447720198977 / 1000000000000000000000000000000)
  directionLo := (44603816205814480158166238213 / 40000000000000000000000000000)
  directionHi := (557547702572681001977077977663 / 500000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree006

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree007
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (44603816205814480158166238213 / 40000000000000000000000000000)
  centralHi := (557547702572681001977077977663 / 500000000000000000000000000000)
  directionLo := (305381453584238522723711019617 / 250000000000000000000000000000)
  directionHi := (1221525814336954090894844078469 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree007

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree008
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (305381453584238522723711019617 / 250000000000000000000000000000)
  centralHi := (1221525814336954090894844078469 / 1000000000000000000000000000000)
  directionLo := (1319398676521550343831028134949 / 1000000000000000000000000000000)
  directionHi := (26387973530431006876620562699 / 20000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree008

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree009
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1319398676521550343831028134949 / 1000000000000000000000000000000)
  centralHi := (26387973530431006876620562699 / 20000000000000000000000000000)
  directionLo := (705248257729517267430094131057 / 500000000000000000000000000000)
  directionHi := (282099303091806906972037652423 / 200000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree009

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree010
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (705248257729517267430094131057 / 500000000000000000000000000000)
  centralHi := (282099303091806906972037652423 / 200000000000000000000000000000)
  directionLo := (46751796136925591270986884327 / 31250000000000000000000000000)
  directionHi := (299211495276323784134316059693 / 200000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree010

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree011
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (46751796136925591270986884327 / 31250000000000000000000000000)
  centralHi := (299211495276323784134316059693 / 200000000000000000000000000000)
  directionLo := (1576983045296492101992712674849 / 1000000000000000000000000000000)
  directionHi := (31539660905929842039854253497 / 20000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree011

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree012
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1576983045296492101992712674849 / 1000000000000000000000000000000)
  centralHi := (31539660905929842039854253497 / 20000000000000000000000000000)
  directionLo := (1653953771321271804668567025707 / 1000000000000000000000000000000)
  directionHi := (413488442830317951167141756427 / 250000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree012

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree013
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1653953771321271804668567025707 / 1000000000000000000000000000000)
  centralHi := (413488442830317951167141756427 / 250000000000000000000000000000)
  directionLo := (1727498373424159746427437658047 / 1000000000000000000000000000000)
  directionHi := (26992162084752496037928713407 / 15625000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree013

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree014
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1727498373424159746427437658047 / 1000000000000000000000000000000)
  centralHi := (26992162084752496037928713407 / 15625000000000000000000000000)
  directionLo := (899018657022530522820595605189 / 500000000000000000000000000000)
  directionHi := (1798037314045061045641191210379 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree014

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree015
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (899018657022530522820595605189 / 500000000000000000000000000000)
  centralHi := (1798037314045061045641191210379 / 1000000000000000000000000000000)
  directionLo := (5830973445355901859741544891 / 3125000000000000000000000000)
  directionHi := (1865911502513888595117294365121 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree015

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree016
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (5830973445355901859741544891 / 3125000000000000000000000000)
  centralHi := (1865911502513888595117294365121 / 1000000000000000000000000000000)
  directionLo := (1931401896998368667359917813613 / 1000000000000000000000000000000)
  directionHi := (965700948499184333679958906807 / 500000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree016

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree017
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1931401896998368667359917813613 / 1000000000000000000000000000000)
  centralHi := (965700948499184333679958906807 / 500000000000000000000000000000)
  directionLo := (1994743301842158560895440397953 / 1000000000000000000000000000000)
  directionHi := (997371650921079280447720198977 / 500000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree017

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree018
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1994743301842158560895440397953 / 1000000000000000000000000000000)
  centralHi := (997371650921079280447720198977 / 500000000000000000000000000000)
  directionLo := (1028067166186068883642287189749 / 500000000000000000000000000000)
  directionHi := (2056134332372137767284574379499 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree018

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree019
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1028067166186068883642287189749 / 500000000000000000000000000000)
  centralHi := (2056134332372137767284574379499 / 1000000000000000000000000000000)
  directionLo := (2115744773188551802290282393171 / 1000000000000000000000000000000)
  directionHi := (528936193297137950572570598293 / 250000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree019

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree020
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (2115744773188551802290282393171 / 1000000000000000000000000000000)
  centralHi := (528936193297137950572570598293 / 250000000000000000000000000000)
  directionLo := (543430279439663740670841407599 / 250000000000000000000000000000)
  directionHi := (2173721117758654962683365630397 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree020

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree021
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (543430279439663740670841407599 / 250000000000000000000000000000)
  centralHi := (2173721117758654962683365630397 / 1000000000000000000000000000000)
  directionLo := (44603816205814480158166238213 / 20000000000000000000000000000)
  directionHi := (2230190810290724007908311910651 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree021

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree022
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (44603816205814480158166238213 / 20000000000000000000000000000)
  centralHi := (2230190810290724007908311910651 / 1000000000000000000000000000000)
  directionLo := (114263277158722958705346698673 / 50000000000000000000000000000)
  directionHi := (2285265543174459174106933973461 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree022

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree023
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (114263277158722958705346698673 / 50000000000000000000000000000)
  centralHi := (2285265543174459174106933973461 / 1000000000000000000000000000000)
  directionLo := (1169521927470335604138674709539 / 500000000000000000000000000000)
  directionHi := (2339043854940671208277349419079 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree023

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree024
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1169521927470335604138674709539 / 500000000000000000000000000000)
  centralHi := (2339043854940671208277349419079 / 1000000000000000000000000000000)
  directionLo := (2391613201972880801915827005959 / 1000000000000000000000000000000)
  directionHi := (59790330049322020047895675149 / 25000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree024

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree025
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (2391613201972880801915827005959 / 1000000000000000000000000000000)
  centralHi := (59790330049322020047895675149 / 25000000000000000000000000000)
  directionLo := (2443051628673908181789688156937 / 1000000000000000000000000000000)
  directionHi := (1221525814336954090894844078469 / 500000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree025

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree026
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (2443051628673908181789688156937 / 1000000000000000000000000000000)
  centralHi := (1221525814336954090894844078469 / 500000000000000000000000000000)
  directionLo := (2493429127302698201119300497441 / 1000000000000000000000000000000)
  directionHi := (1246714563651349100559650248721 / 500000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree026

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree027
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (2493429127302698201119300497441 / 1000000000000000000000000000000)
  centralHi := (1246714563651349100559650248721 / 500000000000000000000000000000)
  directionLo := (2542808755175417229294572960917 / 1000000000000000000000000000000)
  directionHi := (1271404377587708614647286480459 / 500000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree027

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree028
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (2542808755175417229294572960917 / 1000000000000000000000000000000)
  centralHi := (1271404377587708614647286480459 / 500000000000000000000000000000)
  directionLo := (259124756013623961964115648707 / 100000000000000000000000000000)
  directionHi := (2591247560136239619641156487071 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree028

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree029
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (259124756013623961964115648707 / 100000000000000000000000000000)
  centralHi := (2591247560136239619641156487071 / 1000000000000000000000000000000)
  directionLo := (2638797353043100687662056269899 / 1000000000000000000000000000000)
  directionHi := (26387973530431006876620562699 / 10000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree029

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree030
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (2638797353043100687662056269899 / 1000000000000000000000000000000)
  centralHi := (26387973530431006876620562699 / 10000000000000000000000000000)
  directionLo := (1342752678543458945807001895463 / 500000000000000000000000000000)
  directionHi := (2685505357086917891614003790927 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree030

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree031
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1342752678543458945807001895463 / 500000000000000000000000000000)
  centralHi := (2685505357086917891614003790927 / 1000000000000000000000000000000)
  directionLo := (682853689282054136568135760957 / 250000000000000000000000000000)
  directionHi := (2731414757128216546272543043829 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree031

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree032
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (682853689282054136568135760957 / 250000000000000000000000000000)
  centralHi := (2731414757128216546272543043829 / 1000000000000000000000000000000)
  directionLo := (138828258362383250675460112733 / 50000000000000000000000000000)
  directionHi := (2776565167247665013509202254661 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree032

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree033
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (138828258362383250675460112733 / 50000000000000000000000000000)
  centralHi := (2776565167247665013509202254661 / 1000000000000000000000000000000)
  directionLo := (705248257729517267430094131057 / 250000000000000000000000000000)
  directionHi := (2820993030918069069720376524229 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree033

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree034
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (705248257729517267430094131057 / 250000000000000000000000000000)
  centralHi := (2820993030918069069720376524229 / 1000000000000000000000000000000)
  directionLo := (2864731965298599030591295887671 / 1000000000000000000000000000000)
  directionHi := (358091495662324878823911985959 / 125000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree034

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree035
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (2864731965298599030591295887671 / 1000000000000000000000000000000)
  centralHi := (358091495662324878823911985959 / 125000000000000000000000000000)
  directionLo := (1453906529450813200252727702377 / 500000000000000000000000000000)
  directionHi := (581562611780325280101091080951 / 200000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree035

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree036
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1453906529450813200252727702377 / 500000000000000000000000000000)
  centralHi := (581562611780325280101091080951 / 200000000000000000000000000000)
  directionLo := (295026513012544233821527269233 / 100000000000000000000000000000)
  directionHi := (2950265130125442338215272692331 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree036

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree037
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (295026513012544233821527269233 / 100000000000000000000000000000)
  centralHi := (2950265130125442338215272692331 / 1000000000000000000000000000000)
  directionLo := (2992114952763237841343160596929 / 1000000000000000000000000000000)
  directionHi := (299211495276323784134316059693 / 100000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree037

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree038
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (2992114952763237841343160596929 / 1000000000000000000000000000000)
  centralHi := (299211495276323784134316059693 / 100000000000000000000000000000)
  directionLo := (3033387453502208448910769975967 / 1000000000000000000000000000000)
  directionHi := (94793357921944014028461561749 / 31250000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree038

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree039
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3033387453502208448910769975967 / 1000000000000000000000000000000)
  centralHi := (94793357921944014028461561749 / 31250000000000000000000000000)
  directionLo := (192131617846943342351052895107 / 62500000000000000000000000000)
  directionHi := (3074105885551093477616846321713 / 1000000000000000000000000000000)

def shifts : List ℤ := [-16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree039

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree040
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (192131617846943342351052895107 / 62500000000000000000000000000)
  centralHi := (3074105885551093477616846321713 / 1000000000000000000000000000000)
  directionLo := (124571679273228920773696099169 / 40000000000000000000000000000)
  directionHi := (1557145990915361509671201239613 / 500000000000000000000000000000)

def shifts : List ℤ := [-15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree040

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree041
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (124571679273228920773696099169 / 40000000000000000000000000000)
  centralHi := (1557145990915361509671201239613 / 500000000000000000000000000000)
  directionLo := (3153966090592984203985425349699 / 1000000000000000000000000000000)
  directionHi := (31539660905929842039854253497 / 10000000000000000000000000000)

def shifts : List ℤ := [-14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree041

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree042
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3153966090592984203985425349699 / 1000000000000000000000000000000)
  centralHi := (31539660905929842039854253497 / 10000000000000000000000000000)
  directionLo := (127725891834823542477501834837 / 40000000000000000000000000000)
  directionHi := (1596573647935294280968772935463 / 500000000000000000000000000000)

def shifts : List ℤ := [-13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree042

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree043
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (127725891834823542477501834837 / 40000000000000000000000000000)
  centralHi := (1596573647935294280968772935463 / 500000000000000000000000000000)
  directionLo := (3231853524781237955392837799231 / 1000000000000000000000000000000)
  directionHi := (50497711324706843053013090613 / 15625000000000000000000000000)

def shifts : List ℤ := [-12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree043

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree044
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3231853524781237955392837799231 / 1000000000000000000000000000000)
  centralHi := (50497711324706843053013090613 / 15625000000000000000000000000)
  directionLo := (327010164339828612323688415021 / 100000000000000000000000000000)
  directionHi := (3270101643398286123236884150211 / 1000000000000000000000000000000)

def shifts : List ℤ := [-11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree044

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree045
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (327010164339828612323688415021 / 100000000000000000000000000000)
  centralHi := (3270101643398286123236884150211 / 1000000000000000000000000000000)
  directionLo := (661581508528508721867426810283 / 200000000000000000000000000000)
  directionHi := (413488442830317951167141756427 / 125000000000000000000000000000)

def shifts : List ℤ := [-10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree045

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree046
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (661581508528508721867426810283 / 200000000000000000000000000000)
  centralHi := (413488442830317951167141756427 / 125000000000000000000000000000)
  directionLo := (133811448617443440474498714639 / 40000000000000000000000000000)
  directionHi := (418160776929510751482808483247 / 125000000000000000000000000000)

def shifts : List ℤ := [-9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree046

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree047
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (133811448617443440474498714639 / 40000000000000000000000000000)
  centralHi := (418160776929510751482808483247 / 125000000000000000000000000000)
  directionLo := (676450365236118446116726625691 / 200000000000000000000000000000)
  directionHi := (422781478272574028822954141057 / 125000000000000000000000000000)

def shifts : List ℤ := [-8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree047

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree048
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (676450365236118446116726625691 / 200000000000000000000000000000)
  centralHi := (422781478272574028822954141057 / 125000000000000000000000000000)
  directionLo := (1709408886736670361736398181753 / 500000000000000000000000000000)
  directionHi := (3418817773473340723472796363507 / 1000000000000000000000000000000)

def shifts : List ℤ := [-7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree048

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree049
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1709408886736670361736398181753 / 500000000000000000000000000000)
  centralHi := (3418817773473340723472796363507 / 1000000000000000000000000000000)
  directionLo := (1727498373424159746427437658047 / 500000000000000000000000000000)
  directionHi := (690999349369663898570975063219 / 200000000000000000000000000000)

def shifts : List ℤ := [-6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree049

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree050
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1727498373424159746427437658047 / 500000000000000000000000000000)
  centralHi := (690999349369663898570975063219 / 200000000000000000000000000000)
  directionLo := (1745400389111888740783510348209 / 500000000000000000000000000000)
  directionHi := (3490800778223777481567020696419 / 1000000000000000000000000000000)

def shifts : List ℤ := [-5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree050

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree051
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1745400389111888740783510348209 / 500000000000000000000000000000)
  centralHi := (3490800778223777481567020696419 / 1000000000000000000000000000000)
  directionLo := (705248257729517267430094131057 / 200000000000000000000000000000)
  directionHi := (1763120644323793168575235327643 / 500000000000000000000000000000)

def shifts : List ℤ := [-4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree051

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree052
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (705248257729517267430094131057 / 200000000000000000000000000000)
  centralHi := (1763120644323793168575235327643 / 500000000000000000000000000000)
  directionLo := (3561329130855255578269149785591 / 1000000000000000000000000000000)
  directionHi := (445166141356906947283643723199 / 125000000000000000000000000000)

def shifts : List ℤ := [-3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree052

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree053
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3561329130855255578269149785591 / 1000000000000000000000000000000)
  centralHi := (445166141356906947283643723199 / 125000000000000000000000000000)
  directionLo := (3596074628090122091282382420757 / 1000000000000000000000000000000)
  directionHi := (1798037314045061045641191210379 / 500000000000000000000000000000)

def shifts : List ℤ := [-2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree053

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree054
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3596074628090122091282382420757 / 1000000000000000000000000000000)
  centralHi := (1798037314045061045641191210379 / 500000000000000000000000000000)
  directionLo := (1815243804789646549824573907973 / 500000000000000000000000000000)
  directionHi := (3630487609579293099649147815947 / 1000000000000000000000000000000)

def shifts : List ℤ := [-1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree054

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree055
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1815243804789646549824573907973 / 500000000000000000000000000000)
  centralHi := (3630487609579293099649147815947 / 1000000000000000000000000000000)
  directionLo := (1832288721505431136342266117703 / 500000000000000000000000000000)
  directionHi := (3664577443010862272684532235407 / 1000000000000000000000000000000)

def shifts : List ℤ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree055

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree056
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1832288721505431136342266117703 / 500000000000000000000000000000)
  centralHi := (3664577443010862272684532235407 / 1000000000000000000000000000000)
  directionLo := (147934122572660236583033924431 / 40000000000000000000000000000)
  directionHi := (462294133039563239321981013847 / 125000000000000000000000000000)

def shifts : List ℤ := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree056

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree057
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (147934122572660236583033924431 / 40000000000000000000000000000)
  centralHi := (462294133039563239321981013847 / 125000000000000000000000000000)
  directionLo := (5830973445355901859741544891 / 1562500000000000000000000000)
  directionHi := (3731823005027777190234588730241 / 1000000000000000000000000000000)

def shifts : List ℤ := [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree057

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree058
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (5830973445355901859741544891 / 1562500000000000000000000000)
  centralHi := (3731823005027777190234588730241 / 1000000000000000000000000000000)
  directionLo := (470624427180425118213034679889 / 125000000000000000000000000000)
  directionHi := (3764995417443400945704277439113 / 1000000000000000000000000000000)

def shifts : List ℤ := [3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree058

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree059
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (470624427180425118213034679889 / 125000000000000000000000000000)
  centralHi := (3764995417443400945704277439113 / 1000000000000000000000000000000)
  directionLo := (949469524454480211840127591193 / 250000000000000000000000000000)
  directionHi := (3797878097817920847360510364773 / 1000000000000000000000000000000)

def shifts : List ℤ := [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree059

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree060
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (949469524454480211840127591193 / 250000000000000000000000000000)
  centralHi := (3797878097817920847360510364773 / 1000000000000000000000000000000)
  directionLo := (766095701551714191793178602059 / 200000000000000000000000000000)
  directionHi := (478809813469821369870736626287 / 125000000000000000000000000000)

def shifts : List ℤ := [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree060

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree061
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (766095701551714191793178602059 / 200000000000000000000000000000)
  centralHi := (478809813469821369870736626287 / 125000000000000000000000000000)
  directionLo := (1931401896998368667359917813613 / 500000000000000000000000000000)
  directionHi := (3862803793996737334719835627227 / 1000000000000000000000000000000)

def shifts : List ℤ := [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree061

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree062
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1931401896998368667359917813613 / 500000000000000000000000000000)
  centralHi := (3862803793996737334719835627227 / 1000000000000000000000000000000)
  directionLo := (3894860806682422145327026497257 / 1000000000000000000000000000000)
  directionHi := (1947430403341211072663513248629 / 500000000000000000000000000000)

def shifts : List ℤ := [7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree062

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree063
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3894860806682422145327026497257 / 1000000000000000000000000000000)
  centralHi := (1947430403341211072663513248629 / 500000000000000000000000000000)
  directionLo := (196332805816718439575648181653 / 50000000000000000000000000000)
  directionHi := (3926656116334368791512963633061 / 1000000000000000000000000000000)

def shifts : List ℤ := [8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree063

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree064
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (196332805816718439575648181653 / 50000000000000000000000000000)
  centralHi := (3926656116334368791512963633061 / 1000000000000000000000000000000)
  directionLo := (3958196029564651031493084404849 / 1000000000000000000000000000000)
  directionHi := (79163920591293020629861688097 / 20000000000000000000000000000)

def shifts : List ℤ := [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree064

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree065
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3958196029564651031493084404849 / 1000000000000000000000000000000)
  centralHi := (79163920591293020629861688097 / 20000000000000000000000000000)
  directionLo := (1994743301842158560895440397953 / 500000000000000000000000000000)
  directionHi := (3989486603684317121790880795907 / 1000000000000000000000000000000)

def shifts : List ℤ := [10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree065

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree066
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1994743301842158560895440397953 / 500000000000000000000000000000)
  centralHi := (3989486603684317121790880795907 / 1000000000000000000000000000000)
  directionLo := (4020533660285893862487350212267 / 1000000000000000000000000000000)
  directionHi := (1005133415071473465621837553067 / 250000000000000000000000000000)

def shifts : List ℤ := [11, 12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree066

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree067
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (4020533660285893862487350212267 / 1000000000000000000000000000000)
  centralHi := (1005133415071473465621837553067 / 250000000000000000000000000000)
  directionLo := (4051342797889009441059101977613 / 1000000000000000000000000000000)
  directionHi := (2025671398944504720529550988807 / 500000000000000000000000000000)

def shifts : List ℤ := [12, 13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree067

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree068
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (4051342797889009441059101977613 / 1000000000000000000000000000000)
  centralHi := (2025671398944504720529550988807 / 500000000000000000000000000000)
  directionLo := (4081919403726928928701102074713 / 1000000000000000000000000000000)
  directionHi := (2040959701863464464350551037357 / 500000000000000000000000000000)

def shifts : List ℤ := [13, 14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree068

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree069
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (4081919403726928928701102074713 / 1000000000000000000000000000000)
  centralHi := (2040959701863464464350551037357 / 500000000000000000000000000000)
  directionLo := (1028067166186068883642287189749 / 250000000000000000000000000000)
  directionHi := (4112268664744275534569148758997 / 1000000000000000000000000000000)

def shifts : List ℤ := [14, 15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree069

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree070
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1028067166186068883642287189749 / 250000000000000000000000000000)
  centralHi := (4112268664744275534569148758997 / 1000000000000000000000000000000)
  directionLo := (4142395577869516630575957635427 / 1000000000000000000000000000000)
  directionHi := (1035598894467379157643989408857 / 250000000000000000000000000000)

def shifts : List ℤ := [15, 16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree070

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree071
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (4142395577869516630575957635427 / 1000000000000000000000000000000)
  centralHi := (1035598894467379157643989408857 / 250000000000000000000000000000)
  directionLo := (417230495961982462865510196047 / 100000000000000000000000000000)
  directionHi := (4172304959619824628655101960471 / 1000000000000000000000000000000)

def shifts : List ℤ := [16, 17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree071

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree072
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (417230495961982462865510196047 / 100000000000000000000000000000)
  centralHi := (4172304959619824628655101960471 / 1000000000000000000000000000000)
  directionLo := (4202001455090591259224656919079 / 1000000000000000000000000000000)
  directionHi := (105050036377264781480616422977 / 25000000000000000000000000000)

def shifts : List ℤ := [17, 18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree072

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree073
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (4202001455090591259224656919079 / 1000000000000000000000000000000)
  centralHi := (105050036377264781480616422977 / 25000000000000000000000000000)
  directionLo := (2115744773188551802290282393171 / 500000000000000000000000000000)
  directionHi := (4231489546377103604580564786343 / 1000000000000000000000000000000)

def shifts : List ℤ := [18, 19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree073

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree074
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (2115744773188551802290282393171 / 500000000000000000000000000000)
  centralHi := (4231489546377103604580564786343 / 1000000000000000000000000000000)
  directionLo := (1065193390117903832088283864469 / 250000000000000000000000000000)
  directionHi := (4260773560471615328353135457877 / 1000000000000000000000000000000)

def shifts : List ℤ := [19, 20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree074

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree075
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1065193390117903832088283864469 / 250000000000000000000000000000)
  centralHi := (4260773560471615328353135457877 / 1000000000000000000000000000000)
  directionLo := (4289857676675209425399431774859 / 1000000000000000000000000000000)
  directionHi := (214492883833760471269971588743 / 50000000000000000000000000000)

def shifts : List ℤ := [20]

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree075

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree076
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (4289857676675209425399431774859 / 1000000000000000000000000000000)
  centralHi := (214492883833760471269971588743 / 50000000000000000000000000000)
  directionLo := (4318745933560399366068594145117 / 1000000000000000000000000000000)
  directionHi := (2159372966780199683034297072559 / 500000000000000000000000000000)

def shifts : List ℤ := []

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree076

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree077
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (4318745933560399366068594145117 / 1000000000000000000000000000000)
  centralHi := (2159372966780199683034297072559 / 500000000000000000000000000000)
  directionLo := (543430279439663740670841407599 / 125000000000000000000000000000)
  directionHi := (4347442235517309925366731260793 / 1000000000000000000000000000000)

def shifts : List ℤ := []

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree077

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree078
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (543430279439663740670841407599 / 125000000000000000000000000000)
  centralHi := (4347442235517309925366731260793 / 1000000000000000000000000000000)
  directionLo := (4375950358913478930141212421657 / 1000000000000000000000000000000)
  directionHi := (2187975179456739465070606210829 / 500000000000000000000000000000)

def shifts : List ℤ := []

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree078

namespace ForestUnimodality.Stage59KernelData.Cell030.Degree079
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (4375950358913478930141212421657 / 1000000000000000000000000000000)
  centralHi := (2187975179456739465070606210829 / 500000000000000000000000000000)
  directionLo := (440427395789479300116345540629 / 100000000000000000000000000000)
  directionHi := (4404273957894793001163455406291 / 1000000000000000000000000000000)

def shifts : List ℤ := []

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
end ForestUnimodality.Stage59KernelData.Cell030.Degree079
