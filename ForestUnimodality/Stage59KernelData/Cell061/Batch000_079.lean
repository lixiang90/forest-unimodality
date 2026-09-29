import ForestUnimodality.Stage59KernelData.Cell061.Parameters
import ForestUnimodality.FiniteKernelSupportedDegree

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree000
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (0)
  centralHi := (0)
  directionLo := (0)
  directionHi := (0)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree000

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree001
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (0)
  centralHi := (0)
  directionLo := (0)
  directionHi := (0)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree001

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree002
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (0)
  centralHi := (0)
  directionLo := (499835261315966740229109243639 / 1000000000000000000000000000000)
  directionHi := (12495881532899168505727731091 / 25000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree002

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree003
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (499835261315966740229109243639 / 1000000000000000000000000000000)
  centralHi := (12495881532899168505727731091 / 25000000000000000000000000000)
  directionLo := (353436902752670096193211363303 / 500000000000000000000000000000)
  directionHi := (706873805505340192386422726607 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree003

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree004
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (353436902752670096193211363303 / 500000000000000000000000000000)
  centralHi := (706873805505340192386422726607 / 1000000000000000000000000000000)
  directionLo := (865740068013721005065999087133 / 1000000000000000000000000000000)
  directionHi := (432870034006860502532999543567 / 500000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree004

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree005
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (865740068013721005065999087133 / 1000000000000000000000000000000)
  centralHi := (432870034006860502532999543567 / 500000000000000000000000000000)
  directionLo := (499835261315966740229109243639 / 500000000000000000000000000000)
  directionHi := (999670522631933480458218487279 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree005

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree006
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (499835261315966740229109243639 / 500000000000000000000000000000)
  centralHi := (999670522631933480458218487279 / 1000000000000000000000000000000)
  directionLo := (223533124370774524026219165523 / 200000000000000000000000000000)
  directionHi := (34927050682933519379096744613 / 31250000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree006

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree007
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (223533124370774524026219165523 / 200000000000000000000000000000)
  centralHi := (34927050682933519379096744613 / 31250000000000000000000000000)
  directionLo := (122434134567480998037376316777 / 100000000000000000000000000000)
  directionHi := (1224341345674809980373763167771 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree007

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree008
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (122434134567480998037376316777 / 100000000000000000000000000000)
  centralHi := (1224341345674809980373763167771 / 1000000000000000000000000000000)
  directionLo := (1322439797943031242875489931193 / 1000000000000000000000000000000)
  directionHi := (661219898971515621437744965597 / 500000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree008

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree009
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1322439797943031242875489931193 / 1000000000000000000000000000000)
  centralHi := (661219898971515621437744965597 / 500000000000000000000000000000)
  directionLo := (353436902752670096193211363303 / 250000000000000000000000000000)
  directionHi := (1413747611010680384772845453213 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree009

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree010
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (353436902752670096193211363303 / 250000000000000000000000000000)
  centralHi := (1413747611010680384772845453213 / 1000000000000000000000000000000)
  directionLo := (749752891973950110343663865459 / 500000000000000000000000000000)
  directionHi := (1499505783947900220687327730919 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree010

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree011
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (749752891973950110343663865459 / 500000000000000000000000000000)
  centralHi := (1499505783947900220687327730919 / 1000000000000000000000000000000)
  directionLo := (790308940311952875669705159003 / 500000000000000000000000000000)
  directionHi := (1580617880623905751339410318007 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree011

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree012
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (790308940311952875669705159003 / 500000000000000000000000000000)
  centralHi := (1580617880623905751339410318007 / 1000000000000000000000000000000)
  directionLo := (828883009387152344956685776153 / 500000000000000000000000000000)
  directionHi := (1657766018774304689913371552307 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree012

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree013
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (828883009387152344956685776153 / 500000000000000000000000000000)
  centralHi := (1657766018774304689913371552307 / 1000000000000000000000000000000)
  directionLo := (865740068013721005065999087133 / 500000000000000000000000000000)
  directionHi := (1731480136027442010131998174267 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree013

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree014
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (865740068013721005065999087133 / 500000000000000000000000000000)
  centralHi := (1731480136027442010131998174267 / 1000000000000000000000000000000)
  directionLo := (1802181663959660267664715276309 / 1000000000000000000000000000000)
  directionHi := (180218166395966026766471527631 / 100000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree014

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree015
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1802181663959660267664715276309 / 1000000000000000000000000000000)
  centralHi := (180218166395966026766471527631 / 100000000000000000000000000000)
  directionLo := (1870212297672970228015084355371 / 1000000000000000000000000000000)
  directionHi := (467553074418242557003771088843 / 250000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree015

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree016
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1870212297672970228015084355371 / 1000000000000000000000000000000)
  centralHi := (467553074418242557003771088843 / 250000000000000000000000000000)
  directionLo := (1935853642923971501802170314997 / 1000000000000000000000000000000)
  directionHi := (967926821461985750901085157499 / 500000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree016

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree017
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1935853642923971501802170314997 / 1000000000000000000000000000000)
  centralHi := (967926821461985750901085157499 / 500000000000000000000000000000)
  directionLo := (1999341045263866960916436974557 / 1000000000000000000000000000000)
  directionHi := (999670522631933480458218487279 / 500000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree017

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree018
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1999341045263866960916436974557 / 1000000000000000000000000000000)
  centralHi := (999670522631933480458218487279 / 500000000000000000000000000000)
  directionLo := (2060873577813935891276102200433 / 1000000000000000000000000000000)
  directionHi := (1030436788906967945638051100217 / 500000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree018

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree019
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (2060873577813935891276102200433 / 1000000000000000000000000000000)
  centralHi := (1030436788906967945638051100217 / 500000000000000000000000000000)
  directionLo := (1060310708258010288579634089909 / 500000000000000000000000000000)
  directionHi := (2120621416516020577159268179819 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree019

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree020
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1060310708258010288579634089909 / 500000000000000000000000000000)
  centralHi := (2120621416516020577159268179819 / 1000000000000000000000000000000)
  directionLo := (1089365696247271959638411871757 / 500000000000000000000000000000)
  directionHi := (435746278498908783855364748703 / 200000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree020

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree021
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1089365696247271959638411871757 / 500000000000000000000000000000)
  centralHi := (435746278498908783855364748703 / 200000000000000000000000000000)
  directionLo := (2235331243707745240262191655231 / 1000000000000000000000000000000)
  directionHi := (34927050682933519379096744613 / 15625000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree021

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree022
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (2235331243707745240262191655231 / 1000000000000000000000000000000)
  centralHi := (34927050682933519379096744613 / 15625000000000000000000000000)
  directionLo := (286316614998556272169439993849 / 125000000000000000000000000000)
  directionHi := (2290532919988450177355519950793 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree022

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree023
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (286316614998556272169439993849 / 125000000000000000000000000000)
  centralHi := (2290532919988450177355519950793 / 1000000000000000000000000000000)
  directionLo := (146527199186992037704504693031 / 62500000000000000000000000000)
  directionHi := (2344435186991872603272075088497 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree023

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree024
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (146527199186992037704504693031 / 62500000000000000000000000000)
  centralHi := (2344435186991872603272075088497 / 1000000000000000000000000000000)
  directionLo := (2397125702682364009803279138753 / 1000000000000000000000000000000)
  directionHi := (1198562851341182004901639569377 / 500000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree024

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree025
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (2397125702682364009803279138753 / 1000000000000000000000000000000)
  centralHi := (1198562851341182004901639569377 / 500000000000000000000000000000)
  directionLo := (122434134567480998037376316777 / 50000000000000000000000000000)
  directionHi := (2448682691349619960747526335541 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree025

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree026
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (122434134567480998037376316777 / 50000000000000000000000000000)
  centralHi := (2448682691349619960747526335541 / 1000000000000000000000000000000)
  directionLo := (2499176306579833701145546218197 / 1000000000000000000000000000000)
  directionHi := (1249588153289916850572773109099 / 500000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree026

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree027
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (2499176306579833701145546218197 / 1000000000000000000000000000000)
  centralHi := (1249588153289916850572773109099 / 500000000000000000000000000000)
  directionLo := (2548669751031863227308528449227 / 1000000000000000000000000000000)
  directionHi := (637167437757965806827132112307 / 250000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree027

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree028
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (2548669751031863227308528449227 / 1000000000000000000000000000000)
  centralHi := (637167437757965806827132112307 / 250000000000000000000000000000)
  directionLo := (2597220204041163015197997261399 / 1000000000000000000000000000000)
  directionHi := (12986101020205815075989986307 / 5000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree028

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree029
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (2597220204041163015197997261399 / 1000000000000000000000000000000)
  centralHi := (12986101020205815075989986307 / 5000000000000000000000000000)
  directionLo := (1322439797943031242875489931193 / 500000000000000000000000000000)
  directionHi := (2644879595886062485750979862387 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree029

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree030
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1322439797943031242875489931193 / 500000000000000000000000000000)
  centralHi := (2644879595886062485750979862387 / 1000000000000000000000000000000)
  directionLo := (2691695258603622454272560051081 / 1000000000000000000000000000000)
  directionHi := (1345847629301811227136280025541 / 500000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree030

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree031
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (2691695258603622454272560051081 / 1000000000000000000000000000000)
  centralHi := (1345847629301811227136280025541 / 500000000000000000000000000000)
  directionLo := (273771047659244324212978274557 / 100000000000000000000000000000)
  directionHi := (2737710476592443242129782745571 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree031

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree032
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (273771047659244324212978274557 / 100000000000000000000000000000)
  centralHi := (2737710476592443242129782745571 / 1000000000000000000000000000000)
  directionLo := (695741238810217765541378273167 / 250000000000000000000000000000)
  directionHi := (2782964955240871062165513092669 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree032

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree033
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (695741238810217765541378273167 / 250000000000000000000000000000)
  centralHi := (2782964955240871062165513092669 / 1000000000000000000000000000000)
  directionLo := (353436902752670096193211363303 / 125000000000000000000000000000)
  directionHi := (113099808880854430781827636257 / 40000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree033

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree034
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (353436902752670096193211363303 / 125000000000000000000000000000)
  centralHi := (113099808880854430781827636257 / 40000000000000000000000000000)
  directionLo := (2871334971578277035090436208893 / 1000000000000000000000000000000)
  directionHi := (1435667485789138517545218104447 / 500000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree034

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree035
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (2871334971578277035090436208893 / 1000000000000000000000000000000)
  centralHi := (1435667485789138517545218104447 / 500000000000000000000000000000)
  directionLo := (291451536408083217812982247413 / 100000000000000000000000000000)
  directionHi := (2914515364080832178129822474131 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree035

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree036
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (291451536408083217812982247413 / 100000000000000000000000000000)
  centralHi := (2914515364080832178129822474131 / 1000000000000000000000000000000)
  directionLo := (2957065284351704417637748987323 / 1000000000000000000000000000000)
  directionHi := (739266321087926104409437246831 / 250000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree036

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree037
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (2957065284351704417637748987323 / 1000000000000000000000000000000)
  centralHi := (739266321087926104409437246831 / 250000000000000000000000000000)
  directionLo := (749752891973950110343663865459 / 250000000000000000000000000000)
  directionHi := (2999011567895800441374655461837 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree037

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree038
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (749752891973950110343663865459 / 250000000000000000000000000000)
  centralHi := (2999011567895800441374655461837 / 1000000000000000000000000000000)
  directionLo := (3040379198854581694372592829109 / 1000000000000000000000000000000)
  directionHi := (304037919885458169437259282911 / 100000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree038

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree039
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3040379198854581694372592829109 / 1000000000000000000000000000000)
  centralHi := (304037919885458169437259282911 / 100000000000000000000000000000)
  directionLo := (3081191484033802916854440464107 / 1000000000000000000000000000000)
  directionHi := (770297871008450729213610116027 / 250000000000000000000000000000)

def shifts : List ℤ := [-16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree039

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree040
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3081191484033802916854440464107 / 1000000000000000000000000000000)
  centralHi := (770297871008450729213610116027 / 250000000000000000000000000000)
  directionLo := (3121470206447152609492667419409 / 1000000000000000000000000000000)
  directionHi := (312147020644715260949266741941 / 100000000000000000000000000000)

def shifts : List ℤ := [-15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree040

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree041
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3121470206447152609492667419409 / 1000000000000000000000000000000)
  centralHi := (312147020644715260949266741941 / 100000000000000000000000000000)
  directionLo := (3161235761247811502678820636013 / 1000000000000000000000000000000)
  directionHi := (1580617880623905751339410318007 / 500000000000000000000000000000)

def shifts : List ℤ := [-14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree041

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree042
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3161235761247811502678820636013 / 1000000000000000000000000000000)
  centralHi := (1580617880623905751339410318007 / 500000000000000000000000000000)
  directionLo := (3200507276455848185768003574169 / 1000000000000000000000000000000)
  directionHi := (320050727645584818576800357417 / 100000000000000000000000000000)

def shifts : List ℤ := [-13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree042

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree043
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3200507276455848185768003574169 / 1000000000000000000000000000000)
  centralHi := (320050727645584818576800357417 / 100000000000000000000000000000)
  directionLo := (3239302720509713615742447002723 / 1000000000000000000000000000000)
  directionHi := (809825680127428403935611750681 / 250000000000000000000000000000)

def shifts : List ℤ := [-12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree043

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree044
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3239302720509713615742447002723 / 1000000000000000000000000000000)
  centralHi := (809825680127428403935611750681 / 250000000000000000000000000000)
  directionLo := (1638819499178938906831536092297 / 500000000000000000000000000000)
  directionHi := (655527799671575562732614436919 / 200000000000000000000000000000)

def shifts : List ℤ := [-11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree044

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree045
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1638819499178938906831536092297 / 500000000000000000000000000000)
  centralHi := (655527799671575562732614436919 / 200000000000000000000000000000)
  directionLo := (3315532037548609379826743104613 / 1000000000000000000000000000000)
  directionHi := (1657766018774304689913371552307 / 500000000000000000000000000000)

def shifts : List ℤ := [-10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree045

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree046
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3315532037548609379826743104613 / 1000000000000000000000000000000)
  centralHi := (1657766018774304689913371552307 / 500000000000000000000000000000)
  directionLo := (3352996865561617860393287482847 / 1000000000000000000000000000000)
  directionHi := (104781152048800558137290233839 / 31250000000000000000000000000)

def shifts : List ℤ := [-9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree046

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree047
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3352996865561617860393287482847 / 1000000000000000000000000000000)
  centralHi := (104781152048800558137290233839 / 31250000000000000000000000000)
  directionLo := (3390047679446534691910557285441 / 1000000000000000000000000000000)
  directionHi := (1695023839723267345955278642721 / 500000000000000000000000000000)

def shifts : List ℤ := [-8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree047

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree048
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3390047679446534691910557285441 / 1000000000000000000000000000000)
  centralHi := (1695023839723267345955278642721 / 500000000000000000000000000000)
  directionLo := (1713348954341732715542626179459 / 500000000000000000000000000000)
  directionHi := (3426697908683465431085252358919 / 1000000000000000000000000000000)

def shifts : List ℤ := [-7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree048

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree049
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1713348954341732715542626179459 / 500000000000000000000000000000)
  centralHi := (3426697908683465431085252358919 / 1000000000000000000000000000000)
  directionLo := (865740068013721005065999087133 / 250000000000000000000000000000)
  directionHi := (3462960272054884020263996348533 / 1000000000000000000000000000000)

def shifts : List ℤ := [-6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree049

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree050
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (865740068013721005065999087133 / 250000000000000000000000000000)
  centralHi := (3462960272054884020263996348533 / 1000000000000000000000000000000)
  directionLo := (139953873168470687264150588219 / 40000000000000000000000000000)
  directionHi := (874711707302941795400941176369 / 250000000000000000000000000000)

def shifts : List ℤ := [-5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree050

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree051
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (139953873168470687264150588219 / 40000000000000000000000000000)
  centralHi := (874711707302941795400941176369 / 250000000000000000000000000000)
  directionLo := (353436902752670096193211363303 / 100000000000000000000000000000)
  directionHi := (3534369027526700961932113633031 / 1000000000000000000000000000000)

def shifts : List ℤ := [-4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree051

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree052
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (353436902752670096193211363303 / 100000000000000000000000000000)
  centralHi := (3534369027526700961932113633031 / 1000000000000000000000000000000)
  directionLo := (3569537744749989139580054012503 / 1000000000000000000000000000000)
  directionHi := (446192218093748642447506751563 / 125000000000000000000000000000)

def shifts : List ℤ := [-3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree052

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree053
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3569537744749989139580054012503 / 1000000000000000000000000000000)
  centralHi := (446192218093748642447506751563 / 125000000000000000000000000000)
  directionLo := (1802181663959660267664715276309 / 500000000000000000000000000000)
  directionHi := (3604363327919320535329430552619 / 1000000000000000000000000000000)

def shifts : List ℤ := [-2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree053

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree054
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1802181663959660267664715276309 / 500000000000000000000000000000)
  centralHi := (3604363327919320535329430552619 / 1000000000000000000000000000000)
  directionLo := (1819427814458740771237427860611 / 500000000000000000000000000000)
  directionHi := (3638855628917481542474855721223 / 1000000000000000000000000000000)

def shifts : List ℤ := [-1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree054

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree055
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1819427814458740771237427860611 / 500000000000000000000000000000)
  centralHi := (3638855628917481542474855721223 / 1000000000000000000000000000000)
  directionLo := (367302403702442994112128950331 / 100000000000000000000000000000)
  directionHi := (3673024037024429941121289503311 / 1000000000000000000000000000000)

def shifts : List ℤ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree055

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree056
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (367302403702442994112128950331 / 100000000000000000000000000000)
  centralHi := (3673024037024429941121289503311 / 1000000000000000000000000000000)
  directionLo := (1853438754384268941398429634799 / 500000000000000000000000000000)
  directionHi := (3706877508768537882796859269599 / 1000000000000000000000000000000)

def shifts : List ℤ := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree056

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree057
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1853438754384268941398429634799 / 500000000000000000000000000000)
  centralHi := (3706877508768537882796859269599 / 1000000000000000000000000000000)
  directionLo := (1870212297672970228015084355371 / 500000000000000000000000000000)
  directionHi := (3740424595345940456030168710743 / 1000000000000000000000000000000)

def shifts : List ℤ := [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree057

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree058
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1870212297672970228015084355371 / 500000000000000000000000000000)
  centralHi := (3740424595345940456030168710743 / 1000000000000000000000000000000)
  directionLo := (1886836733922919678182972992757 / 500000000000000000000000000000)
  directionHi := (754734693569167871273189197103 / 200000000000000000000000000000)

def shifts : List ℤ := [3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree058

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree059
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1886836733922919678182972992757 / 500000000000000000000000000000)
  centralHi := (754734693569167871273189197103 / 200000000000000000000000000000)
  directionLo := (3806631940492598231027971939081 / 1000000000000000000000000000000)
  directionHi := (1903315970246299115513985969541 / 500000000000000000000000000000)

def shifts : List ℤ := [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree059

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree060
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3806631940492598231027971939081 / 1000000000000000000000000000000)
  centralHi := (1903315970246299115513985969541 / 500000000000000000000000000000)
  directionLo := (239956718255745784026331434663 / 62500000000000000000000000000)
  directionHi := (3839307492091932544421302954609 / 1000000000000000000000000000000)

def shifts : List ℤ := [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree060

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree061
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (239956718255745784026331434663 / 62500000000000000000000000000)
  centralHi := (3839307492091932544421302954609 / 1000000000000000000000000000000)
  directionLo := (1935853642923971501802170314997 / 500000000000000000000000000000)
  directionHi := (774341457169588600720868125999 / 200000000000000000000000000000)

def shifts : List ℤ := [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree061

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree062
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1935853642923971501802170314997 / 500000000000000000000000000000)
  centralHi := (774341457169588600720868125999 / 200000000000000000000000000000)
  directionLo := (3903838187699747141198309360587 / 1000000000000000000000000000000)
  directionHi := (975959546924936785299577340147 / 250000000000000000000000000000)

def shifts : List ℤ := [7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree062

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree063
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3903838187699747141198309360587 / 1000000000000000000000000000000)
  centralHi := (975959546924936785299577340147 / 250000000000000000000000000000)
  directionLo := (3935706783310673278596795969327 / 1000000000000000000000000000000)
  directionHi := (245981673956917079912299748083 / 62500000000000000000000000000)

def shifts : List ℤ := [8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree063

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree064
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3935706783310673278596795969327 / 1000000000000000000000000000000)
  centralHi := (245981673956917079912299748083 / 62500000000000000000000000000)
  directionLo := (198365969691454686431323489679 / 50000000000000000000000000000)
  directionHi := (3967319393829093728626469793581 / 1000000000000000000000000000000)

def shifts : List ℤ := [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree064

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree065
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (198365969691454686431323489679 / 50000000000000000000000000000)
  centralHi := (3967319393829093728626469793581 / 1000000000000000000000000000000)
  directionLo := (799736418105546784366574789823 / 200000000000000000000000000000)
  directionHi := (999670522631933480458218487279 / 250000000000000000000000000000)

def shifts : List ℤ := [10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree065

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree066
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (799736418105546784366574789823 / 200000000000000000000000000000)
  centralHi := (999670522631933480458218487279 / 250000000000000000000000000000)
  directionLo := (4029800708417483171028896446779 / 1000000000000000000000000000000)
  directionHi := (201490035420874158551444822339 / 50000000000000000000000000000)

def shifts : List ℤ := [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree066

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree067
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (4029800708417483171028896446779 / 1000000000000000000000000000000)
  centralHi := (201490035420874158551444822339 / 50000000000000000000000000000)
  directionLo := (4060680858922164788965037559421 / 1000000000000000000000000000000)
  directionHi := (2030340429461082394482518779711 / 500000000000000000000000000000)

def shifts : List ℤ := [12, 13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree067

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree068
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (4060680858922164788965037559421 / 1000000000000000000000000000000)
  centralHi := (2030340429461082394482518779711 / 500000000000000000000000000000)
  directionLo := (4091327941692238722395093354473 / 1000000000000000000000000000000)
  directionHi := (2045663970846119361197546677237 / 500000000000000000000000000000)

def shifts : List ℤ := [13, 14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree068

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree069
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (4091327941692238722395093354473 / 1000000000000000000000000000000)
  centralHi := (2045663970846119361197546677237 / 500000000000000000000000000000)
  directionLo := (2060873577813935891276102200433 / 500000000000000000000000000000)
  directionHi := (4121747155627871782552204400867 / 1000000000000000000000000000000)

def shifts : List ℤ := [14, 15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree069

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree070
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (2060873577813935891276102200433 / 500000000000000000000000000000)
  centralHi := (4121747155627871782552204400867 / 1000000000000000000000000000000)
  directionLo := (415194350917510102983454680227 / 100000000000000000000000000000)
  directionHi := (4151943509175101029834546802271 / 1000000000000000000000000000000)

def shifts : List ℤ := [15, 16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree070

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree071
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (415194350917510102983454680227 / 100000000000000000000000000000)
  centralHi := (4151943509175101029834546802271 / 1000000000000000000000000000000)
  directionLo := (4181921829952833181813595324821 / 1000000000000000000000000000000)
  directionHi := (2090960914976416590906797662411 / 500000000000000000000000000000)

def shifts : List ℤ := [16, 17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree071

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree072
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (4181921829952833181813595324821 / 1000000000000000000000000000000)
  centralHi := (2090960914976416590906797662411 / 500000000000000000000000000000)
  directionLo := (1052921693440769772921350049611 / 250000000000000000000000000000)
  directionHi := (842337354752615818337080039689 / 200000000000000000000000000000)

def shifts : List ℤ := [17, 18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree072

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree073
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1052921693440769772921350049611 / 250000000000000000000000000000)
  centralHi := (842337354752615818337080039689 / 200000000000000000000000000000)
  directionLo := (1060310708258010288579634089909 / 250000000000000000000000000000)
  directionHi := (4241242833032041154318536359637 / 1000000000000000000000000000000)

def shifts : List ℤ := [18, 19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree073

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree074
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1060310708258010288579634089909 / 250000000000000000000000000000)
  centralHi := (4241242833032041154318536359637 / 1000000000000000000000000000000)
  directionLo := (1067648586181346682770510244837 / 250000000000000000000000000000)
  directionHi := (4270594344725386731082040979349 / 1000000000000000000000000000000)

def shifts : List ℤ := [19, 20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree074

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree075
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1067648586181346682770510244837 / 250000000000000000000000000000)
  centralHi := (4270594344725386731082040979349 / 1000000000000000000000000000000)
  directionLo := (1074936374444298680897737320839 / 250000000000000000000000000000)
  directionHi := (4299745497777194723590949283357 / 1000000000000000000000000000000)

def shifts : List ℤ := [20, 21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree075

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree076
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1074936374444298680897737320839 / 250000000000000000000000000000)
  centralHi := (4299745497777194723590949283357 / 1000000000000000000000000000000)
  directionLo := (865740068013721005065999087133 / 200000000000000000000000000000)
  directionHi := (2164350170034302512664997717833 / 500000000000000000000000000000)

def shifts : List ℤ := [21]

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree076

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree077
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (865740068013721005065999087133 / 200000000000000000000000000000)
  centralHi := (2164350170034302512664997717833 / 500000000000000000000000000000)
  directionLo := (4357462784989087838553647487029 / 1000000000000000000000000000000)
  directionHi := (435746278498908783855364748703 / 100000000000000000000000000000)

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree077

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree078
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (4357462784989087838553647487029 / 1000000000000000000000000000000)
  centralHi := (435746278498908783855364748703 / 100000000000000000000000000000)
  directionLo := (4386036617610443332517896228571 / 1000000000000000000000000000000)
  directionHi := (1096509154402610833129474057143 / 250000000000000000000000000000)

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree078

namespace ForestUnimodality.Stage59KernelData.Cell061.Degree079
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (4386036617610443332517896228571 / 1000000000000000000000000000000)
  centralHi := (1096509154402610833129474057143 / 250000000000000000000000000000)
  directionLo := (1103606375125277033908909495963 / 250000000000000000000000000000)
  directionHi := (4414425500501108135635637983853 / 1000000000000000000000000000000)

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
end ForestUnimodality.Stage59KernelData.Cell061.Degree079
