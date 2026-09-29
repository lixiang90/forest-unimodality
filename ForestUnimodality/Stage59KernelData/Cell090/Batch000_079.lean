import ForestUnimodality.Stage59KernelData.Cell090.Parameters
import ForestUnimodality.FiniteKernelSupportedDegree

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree000
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (0)
  centralHi := (0)
  directionLo := (0)
  directionHi := (0)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree000

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree001
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (0)
  centralHi := (0)
  directionLo := (0)
  directionHi := (0)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree001

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree002
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (0)
  centralHi := (0)
  directionLo := (49999362305901832946060258223 / 100000000000000000000000000000)
  directionHi := (499993623059018329460602582231 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree002

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree003
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (49999362305901832946060258223 / 100000000000000000000000000000)
  centralHi := (499993623059018329460602582231 / 1000000000000000000000000000000)
  directionLo := (707097762830124793125505916729 / 1000000000000000000000000000000)
  directionHi := (70709776283012479312550591673 / 100000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree003

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree004
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (707097762830124793125505916729 / 1000000000000000000000000000000)
  centralHi := (70709776283012479312550591673 / 100000000000000000000000000000)
  directionLo := (433007179299330762618412555509 / 500000000000000000000000000000)
  directionHi := (866014358598661525236825111019 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree004

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree005
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (433007179299330762618412555509 / 500000000000000000000000000000)
  centralHi := (866014358598661525236825111019 / 1000000000000000000000000000000)
  directionLo := (999987246118036658921205164461 / 1000000000000000000000000000000)
  directionHi := (499993623059018329460602582231 / 500000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree005

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree006
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (999987246118036658921205164461 / 1000000000000000000000000000000)
  centralHi := (499993623059018329460602582231 / 500000000000000000000000000000)
  directionLo := (559009864738185664319039351639 / 500000000000000000000000000000)
  directionHi := (1118019729476371328638078703279 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree006

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree007
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (559009864738185664319039351639 / 500000000000000000000000000000)
  centralHi := (1118019729476371328638078703279 / 1000000000000000000000000000000)
  directionLo := (1224729251140064113421854114611 / 1000000000000000000000000000000)
  directionHi := (306182312785016028355463528653 / 250000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree007

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree008
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1224729251140064113421854114611 / 1000000000000000000000000000000)
  centralHi := (306182312785016028355463528653 / 250000000000000000000000000000)
  directionLo := (1322858783732332458903843481553 / 1000000000000000000000000000000)
  directionHi := (661429391866166229451921740777 / 500000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree008

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree009
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1322858783732332458903843481553 / 1000000000000000000000000000000)
  centralHi := (661429391866166229451921740777 / 500000000000000000000000000000)
  directionLo := (707097762830124793125505916729 / 500000000000000000000000000000)
  directionHi := (1414195525660249586251011833459 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree009

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree010
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (707097762830124793125505916729 / 500000000000000000000000000000)
  centralHi := (1414195525660249586251011833459 / 1000000000000000000000000000000)
  directionLo := (374995217294263747095451936673 / 250000000000000000000000000000)
  directionHi := (1499980869177054988381807746693 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree010

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree011
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (374995217294263747095451936673 / 250000000000000000000000000000)
  centralHi := (1499980869177054988381807746693 / 1000000000000000000000000000000)
  directionLo := (1581118664426183117038167478089 / 1000000000000000000000000000000)
  directionHi := (158111866442618311703816747809 / 100000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree011

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree012
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1581118664426183117038167478089 / 1000000000000000000000000000000)
  centralHi := (158111866442618311703816747809 / 100000000000000000000000000000)
  directionLo := (1658291245257153482747025520359 / 1000000000000000000000000000000)
  directionHi := (41457281131428837068675638009 / 25000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree012

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree013
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1658291245257153482747025520359 / 1000000000000000000000000000000)
  centralHi := (41457281131428837068675638009 / 25000000000000000000000000000)
  directionLo := (1732028717197323050473650222037 / 1000000000000000000000000000000)
  directionHi := (866014358598661525236825111019 / 500000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree013

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree014
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1732028717197323050473650222037 / 1000000000000000000000000000000)
  centralHi := (866014358598661525236825111019 / 500000000000000000000000000000)
  directionLo := (1802752645344304625762317988059 / 1000000000000000000000000000000)
  directionHi := (90137632267215231288115899403 / 50000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree014

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree015
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1802752645344304625762317988059 / 1000000000000000000000000000000)
  centralHi := (90137632267215231288115899403 / 50000000000000000000000000000)
  directionLo := (374160966611728320749796054817 / 200000000000000000000000000000)
  directionHi := (935402416529320801874490137043 / 500000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree015

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree016
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (374160966611728320749796054817 / 200000000000000000000000000000)
  centralHi := (935402416529320801874490137043 / 500000000000000000000000000000)
  directionLo := (387293395063497337002810454777 / 200000000000000000000000000000)
  directionHi := (968233487658743342507026136943 / 500000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree016

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree017
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (387293395063497337002810454777 / 200000000000000000000000000000)
  centralHi := (968233487658743342507026136943 / 500000000000000000000000000000)
  directionLo := (1999974492236073317842410328923 / 1000000000000000000000000000000)
  directionHi := (499993623059018329460602582231 / 250000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree017

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree018
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1999974492236073317842410328923 / 1000000000000000000000000000000)
  centralHi := (499993623059018329460602582231 / 250000000000000000000000000000)
  directionLo := (1030763260003797258651472866683 / 500000000000000000000000000000)
  directionHi := (2061526520007594517302945733367 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree018

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree019
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1030763260003797258651472866683 / 500000000000000000000000000000)
  centralHi := (2061526520007594517302945733367 / 1000000000000000000000000000000)
  directionLo := (2121293288490374379376517750187 / 1000000000000000000000000000000)
  directionHi := (530323322122593594844129437547 / 250000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree019

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree020
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (2121293288490374379376517750187 / 1000000000000000000000000000000)
  centralHi := (530323322122593594844129437547 / 250000000000000000000000000000)
  directionLo := (2179421675329028751178604382361 / 1000000000000000000000000000000)
  directionHi := (1089710837664514375589302191181 / 500000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree020

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree021
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (2179421675329028751178604382361 / 1000000000000000000000000000000)
  centralHi := (1089710837664514375589302191181 / 500000000000000000000000000000)
  directionLo := (2236039458952742657276157406557 / 1000000000000000000000000000000)
  directionHi := (1118019729476371328638078703279 / 500000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree021

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree022
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (2236039458952742657276157406557 / 1000000000000000000000000000000)
  centralHi := (1118019729476371328638078703279 / 500000000000000000000000000000)
  directionLo := (143203664041448077002834699327 / 62500000000000000000000000000)
  directionHi := (2291258624663169232045355189233 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree022

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree023
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (143203664041448077002834699327 / 62500000000000000000000000000)
  centralHi := (2291258624663169232045355189233 / 1000000000000000000000000000000)
  directionLo := (2345177969407234885893007349819 / 1000000000000000000000000000000)
  directionHi := (117258898470361744294650367491 / 50000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree023

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree024
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (2345177969407234885893007349819 / 1000000000000000000000000000000)
  centralHi := (117258898470361744294650367491 / 50000000000000000000000000000)
  directionLo := (2397885178921777570466615900591 / 1000000000000000000000000000000)
  directionHi := (149867823682611098154163493787 / 62500000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree024

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree025
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (2397885178921777570466615900591 / 1000000000000000000000000000000)
  centralHi := (149867823682611098154163493787 / 62500000000000000000000000000)
  directionLo := (1224729251140064113421854114611 / 500000000000000000000000000000)
  directionHi := (2449458502280128226843708229223 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree025

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree026
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1224729251140064113421854114611 / 500000000000000000000000000000)
  centralHi := (2449458502280128226843708229223 / 1000000000000000000000000000000)
  directionLo := (1249984057647545823651506455577 / 500000000000000000000000000000)
  directionHi := (499993623059018329460602582231 / 200000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree026

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree027
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1249984057647545823651506455577 / 500000000000000000000000000000)
  centralHi := (499993623059018329460602582231 / 200000000000000000000000000000)
  directionLo := (2549477240649889847404511466457 / 1000000000000000000000000000000)
  directionHi := (1274738620324944923702255733229 / 500000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree027

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree028
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (2549477240649889847404511466457 / 1000000000000000000000000000000)
  centralHi := (1274738620324944923702255733229 / 500000000000000000000000000000)
  directionLo := (40594423059312258995476177079 / 15625000000000000000000000000)
  directionHi := (2598043075795984575710475333057 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree028

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree029
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (40594423059312258995476177079 / 15625000000000000000000000000)
  centralHi := (2598043075795984575710475333057 / 1000000000000000000000000000000)
  directionLo := (2645717567464664917807686963107 / 1000000000000000000000000000000)
  directionHi := (661429391866166229451921740777 / 250000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree029

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree030
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (2645717567464664917807686963107 / 1000000000000000000000000000000)
  centralHi := (661429391866166229451921740777 / 250000000000000000000000000000)
  directionLo := (1346274031344550174840127241031 / 500000000000000000000000000000)
  directionHi := (2692548062689100349680254482063 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree030

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree031
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1346274031344550174840127241031 / 500000000000000000000000000000)
  centralHi := (2692548062689100349680254482063 / 1000000000000000000000000000000)
  directionLo := (2738577859581595166360231135207 / 1000000000000000000000000000000)
  directionHi := (342322232447699395795028891901 / 125000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree031

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree032
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (2738577859581595166360231135207 / 1000000000000000000000000000000)
  centralHi := (342322232447699395795028891901 / 125000000000000000000000000000)
  directionLo := (69596166902756733638361063531 / 25000000000000000000000000000)
  directionHi := (2783846676110269345534442541241 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree032

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree033
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (69596166902756733638361063531 / 25000000000000000000000000000)
  centralHi := (2783846676110269345534442541241 / 1000000000000000000000000000000)
  directionLo := (2828391051320499172502023666917 / 1000000000000000000000000000000)
  directionHi := (1414195525660249586251011833459 / 500000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree033

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree034
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (2828391051320499172502023666917 / 1000000000000000000000000000000)
  centralHi := (1414195525660249586251011833459 / 500000000000000000000000000000)
  directionLo := (2872244690532051847796994342001 / 1000000000000000000000000000000)
  directionHi := (1436122345266025923898497171001 / 500000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree034

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree035
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (2872244690532051847796994342001 / 1000000000000000000000000000000)
  centralHi := (1436122345266025923898497171001 / 500000000000000000000000000000)
  directionLo := (2915438763786549846954878521223 / 1000000000000000000000000000000)
  directionHi := (364429845473318730869359815153 / 125000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree035

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree036
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (2915438763786549846954878521223 / 1000000000000000000000000000000)
  centralHi := (364429845473318730869359815153 / 125000000000000000000000000000)
  directionLo := (2958002165058188340786344098081 / 1000000000000000000000000000000)
  directionHi := (1479001082529094170393172049041 / 500000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree036

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree037
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (2958002165058188340786344098081 / 1000000000000000000000000000000)
  centralHi := (1479001082529094170393172049041 / 500000000000000000000000000000)
  directionLo := (599992347670821995352723098677 / 200000000000000000000000000000)
  directionHi := (1499980869177054988381807746693 / 500000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree037

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree038
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (599992347670821995352723098677 / 200000000000000000000000000000)
  centralHi := (1499980869177054988381807746693 / 500000000000000000000000000000)
  directionLo := (1520671237865724307898317148943 / 500000000000000000000000000000)
  directionHi := (3041342475731448615796634297887 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree038

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree039
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1520671237865724307898317148943 / 500000000000000000000000000000)
  centralHi := (3041342475731448615796634297887 / 1000000000000000000000000000000)
  directionLo := (770541922845051177130261995473 / 250000000000000000000000000000)
  directionHi := (3082167691380204708521047981893 / 1000000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree039

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree040
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (770541922845051177130261995473 / 250000000000000000000000000000)
  centralHi := (3082167691380204708521047981893 / 1000000000000000000000000000000)
  directionLo := (3122459175215532665688368217307 / 1000000000000000000000000000000)
  directionHi := (780614793803883166422092054327 / 250000000000000000000000000000)

def shifts : List ℤ := [-17, -16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree040

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree041
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3122459175215532665688368217307 / 1000000000000000000000000000000)
  centralHi := (780614793803883166422092054327 / 250000000000000000000000000000)
  directionLo := (3162237328852366234076334956179 / 1000000000000000000000000000000)
  directionHi := (158111866442618311703816747809 / 50000000000000000000000000000)

def shifts : List ℤ := [-16, -15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree041

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree042
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3162237328852366234076334956179 / 1000000000000000000000000000000)
  centralHi := (158111866442618311703816747809 / 50000000000000000000000000000)
  directionLo := (3201521286371063929790016639239 / 1000000000000000000000000000000)
  directionHi := (80038032159276598244750415981 / 25000000000000000000000000000)

def shifts : List ℤ := [-15, -14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree042

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree043
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3201521286371063929790016639239 / 1000000000000000000000000000000)
  centralHi := (80038032159276598244750415981 / 25000000000000000000000000000)
  directionLo := (1620164510951489429122830809911 / 500000000000000000000000000000)
  directionHi := (3240329021902978858245661619823 / 1000000000000000000000000000000)

def shifts : List ℤ := [-14, -13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree043

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree044
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1620164510951489429122830809911 / 500000000000000000000000000000)
  centralHi := (3240329021902978858245661619823 / 1000000000000000000000000000000)
  directionLo := (16393387228762699597793990437 / 5000000000000000000000000000)
  directionHi := (3278677445752539919558798087401 / 1000000000000000000000000000000)

def shifts : List ℤ := [-13, -12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree044

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree045
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (16393387228762699597793990437 / 5000000000000000000000000000)
  centralHi := (3278677445752539919558798087401 / 1000000000000000000000000000000)
  directionLo := (3316582490514306965494051040719 / 1000000000000000000000000000000)
  directionHi := (41457281131428837068675638009 / 12500000000000000000000000000)

def shifts : List ℤ := [-12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree045

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree046
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3316582490514306965494051040719 / 1000000000000000000000000000000)
  centralHi := (41457281131428837068675638009 / 12500000000000000000000000000)
  directionLo := (838514797107278496478559027459 / 250000000000000000000000000000)
  directionHi := (3354059188429113985914236109837 / 1000000000000000000000000000000)

def shifts : List ℤ := [-11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree046

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree047
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (838514797107278496478559027459 / 250000000000000000000000000000)
  centralHi := (3354059188429113985914236109837 / 1000000000000000000000000000000)
  directionLo := (3391121741044613465151965575651 / 1000000000000000000000000000000)
  directionHi := (847780435261153366287991393913 / 250000000000000000000000000000)

def shifts : List ℤ := [-10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree047

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree048
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3391121741044613465151965575651 / 1000000000000000000000000000000)
  centralHi := (847780435261153366287991393913 / 250000000000000000000000000000)
  directionLo := (1713891791047872293442057787213 / 500000000000000000000000000000)
  directionHi := (3427783582095744586884115574427 / 1000000000000000000000000000000)

def shifts : List ℤ := [-9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree048

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree049
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1713891791047872293442057787213 / 500000000000000000000000000000)
  centralHi := (3427783582095744586884115574427 / 1000000000000000000000000000000)
  directionLo := (138562297375785844037892017763 / 40000000000000000000000000000)
  directionHi := (866014358598661525236825111019 / 250000000000000000000000000000)

def shifts : List ℤ := [-8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree049

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree050
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (138562297375785844037892017763 / 40000000000000000000000000000)
  centralHi := (866014358598661525236825111019 / 250000000000000000000000000000)
  directionLo := (109373605044160259569506814863 / 31250000000000000000000000000)
  directionHi := (3499955361413128306224218075617 / 1000000000000000000000000000000)

def shifts : List ℤ := [-7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree050

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree051
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (109373605044160259569506814863 / 31250000000000000000000000000)
  centralHi := (3499955361413128306224218075617 / 1000000000000000000000000000000)
  directionLo := (1767744407075311982813764791823 / 500000000000000000000000000000)
  directionHi := (3535488814150623965627529583647 / 1000000000000000000000000000000)

def shifts : List ℤ := [-6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree051

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree052
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1767744407075311982813764791823 / 500000000000000000000000000000)
  centralHi := (3535488814150623965627529583647 / 1000000000000000000000000000000)
  directionLo := (1785334336901905678530158975147 / 500000000000000000000000000000)
  directionHi := (714133734760762271412063590059 / 200000000000000000000000000000)

def shifts : List ℤ := [-5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree052

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree053
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1785334336901905678530158975147 / 500000000000000000000000000000)
  centralHi := (714133734760762271412063590059 / 200000000000000000000000000000)
  directionLo := (3605505290688609251524635976119 / 1000000000000000000000000000000)
  directionHi := (90137632267215231288115899403 / 25000000000000000000000000000)

def shifts : List ℤ := [-4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree053

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree054
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3605505290688609251524635976119 / 1000000000000000000000000000000)
  centralHi := (90137632267215231288115899403 / 25000000000000000000000000000)
  directionLo := (1820004259904577558819292536403 / 500000000000000000000000000000)
  directionHi := (3640008519809155117638585072807 / 1000000000000000000000000000000)

def shifts : List ℤ := [-3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree054

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree055
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1820004259904577558819292536403 / 500000000000000000000000000000)
  centralHi := (3640008519809155117638585072807 / 1000000000000000000000000000000)
  directionLo := (1837093876710096170132781171917 / 500000000000000000000000000000)
  directionHi := (734837550684038468053112468767 / 200000000000000000000000000000)

def shifts : List ℤ := [-2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree055

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree056
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1837093876710096170132781171917 / 500000000000000000000000000000)
  centralHi := (734837550684038468053112468767 / 200000000000000000000000000000)
  directionLo := (927012987721942727742427262923 / 250000000000000000000000000000)
  directionHi := (3708051950887770910969709051693 / 1000000000000000000000000000000)

def shifts : List ℤ := [-1, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree056

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree057
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (927012987721942727742427262923 / 250000000000000000000000000000)
  centralHi := (3708051950887770910969709051693 / 1000000000000000000000000000000)
  directionLo := (374160966611728320749796054817 / 100000000000000000000000000000)
  directionHi := (3741609666117283207497960548171 / 1000000000000000000000000000000)

def shifts : List ℤ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree057

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree058
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (374160966611728320749796054817 / 100000000000000000000000000000)
  centralHi := (3741609666117283207497960548171 / 1000000000000000000000000000000)
  directionLo := (3774869072786759743121334671143 / 1000000000000000000000000000000)
  directionHi := (471858634098344967890166833893 / 125000000000000000000000000000)

def shifts : List ℤ := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree058

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree059
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3774869072786759743121334671143 / 1000000000000000000000000000000)
  centralHi := (471858634098344967890166833893 / 125000000000000000000000000000)
  directionLo := (761567597519265650989328115487 / 200000000000000000000000000000)
  directionHi := (951959496899082063736660144359 / 250000000000000000000000000000)

def shifts : List ℤ := [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree059

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree060
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (761567597519265650989328115487 / 200000000000000000000000000000)
  centralHi := (951959496899082063736660144359 / 250000000000000000000000000000)
  directionLo := (3840523891721198320153122759621 / 1000000000000000000000000000000)
  directionHi := (1920261945860599160076561379811 / 500000000000000000000000000000)

def shifts : List ℤ := [3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree060

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree061
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3840523891721198320153122759621 / 1000000000000000000000000000000)
  centralHi := (1920261945860599160076561379811 / 500000000000000000000000000000)
  directionLo := (3872933950634973370028104547771 / 1000000000000000000000000000000)
  directionHi := (968233487658743342507026136943 / 250000000000000000000000000000)

def shifts : List ℤ := [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree061

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree062
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3872933950634973370028104547771 / 1000000000000000000000000000000)
  centralHi := (968233487658743342507026136943 / 250000000000000000000000000000)
  directionLo := (78101500649041836577440269471 / 20000000000000000000000000000)
  directionHi := (3905075032452091828872013473551 / 1000000000000000000000000000000)

def shifts : List ℤ := [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree062

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree063
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (78101500649041836577440269471 / 20000000000000000000000000000)
  centralHi := (3905075032452091828872013473551 / 1000000000000000000000000000000)
  directionLo := (3936953724922403727407452664863 / 1000000000000000000000000000000)
  directionHi := (123029803903825116481482895777 / 31250000000000000000000000000)

def shifts : List ℤ := [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree063

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree064
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3936953724922403727407452664863 / 1000000000000000000000000000000)
  centralHi := (123029803903825116481482895777 / 31250000000000000000000000000)
  directionLo := (198428817559849868835576522233 / 50000000000000000000000000000)
  directionHi := (3968576351196997376711530444661 / 1000000000000000000000000000000)

def shifts : List ℤ := [7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree064

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree065
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (198428817559849868835576522233 / 50000000000000000000000000000)
  centralHi := (3968576351196997376711530444661 / 1000000000000000000000000000000)
  directionLo := (3999948984472146635684820657847 / 1000000000000000000000000000000)
  directionHi := (499993623059018329460602582231 / 125000000000000000000000000000)

def shifts : List ℤ := [8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree065

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree066
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (3999948984472146635684820657847 / 1000000000000000000000000000000)
  centralHi := (499993623059018329460602582231 / 125000000000000000000000000000)
  directionLo := (2015538730803717455158776602171 / 500000000000000000000000000000)
  directionHi := (4031077461607434910317553204343 / 1000000000000000000000000000000)

def shifts : List ℤ := [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree066

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree067
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (2015538730803717455158776602171 / 500000000000000000000000000000)
  centralHi := (4031077461607434910317553204343 / 1000000000000000000000000000000)
  directionLo := (2030983697902270495913058216279 / 500000000000000000000000000000)
  directionHi := (4061967395804540991826116432559 / 1000000000000000000000000000000)

def shifts : List ℤ := [10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree067

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree068
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (2030983697902270495913058216279 / 500000000000000000000000000000)
  centralHi := (4061967395804540991826116432559 / 1000000000000000000000000000000)
  directionLo := (1023156047106171150251254572289 / 250000000000000000000000000000)
  directionHi := (4092624188424684601005018289157 / 1000000000000000000000000000000)

def shifts : List ℤ := [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree068

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree069
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1023156047106171150251254572289 / 250000000000000000000000000000)
  centralHi := (4092624188424684601005018289157 / 1000000000000000000000000000000)
  directionLo := (1030763260003797258651472866683 / 250000000000000000000000000000)
  directionHi := (4123053040015189034605891466733 / 1000000000000000000000000000000)

def shifts : List ℤ := [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree069

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree070
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (1030763260003797258651472866683 / 250000000000000000000000000000)
  centralHi := (4123053040015189034605891466733 / 1000000000000000000000000000000)
  directionLo := (4153258960608906661575798685187 / 1000000000000000000000000000000)
  directionHi := (1038314740152226665393949671297 / 250000000000000000000000000000)

def shifts : List ℤ := [13, 14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree070

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree071
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (4153258960608906661575798685187 / 1000000000000000000000000000000)
  centralHi := (1038314740152226665393949671297 / 250000000000000000000000000000)
  directionLo := (4183246779354268432818211251619 / 1000000000000000000000000000000)
  directionHi := (209162338967713421640910562581 / 50000000000000000000000000000)

def shifts : List ℤ := [14, 15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree071

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree072
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (4183246779354268432818211251619 / 1000000000000000000000000000000)
  centralHi := (209162338967713421640910562581 / 50000000000000000000000000000)
  directionLo := (842604230705674610615157290333 / 200000000000000000000000000000)
  directionHi := (2106510576764186526537893225833 / 500000000000000000000000000000)

def shifts : List ℤ := [15, 16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree072

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree073
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (842604230705674610615157290333 / 200000000000000000000000000000)
  centralHi := (2106510576764186526537893225833 / 500000000000000000000000000000)
  directionLo := (33940692615845990070024284003 / 8000000000000000000000000000)
  directionHi := (530323322122593594844129437547 / 125000000000000000000000000000)

def shifts : List ℤ := [16, 17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree073

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree074
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (33940692615845990070024284003 / 8000000000000000000000000000)
  centralHi := (530323322122593594844129437547 / 125000000000000000000000000000)
  directionLo := (854389477610226904398667819447 / 200000000000000000000000000000)
  directionHi := (1067986847012783630498334774309 / 250000000000000000000000000000)

def shifts : List ℤ := [17, 18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree074

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree075
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (854389477610226904398667819447 / 200000000000000000000000000000)
  centralHi := (1067986847012783630498334774309 / 250000000000000000000000000000)
  directionLo := (43011077770007803217714012837 / 10000000000000000000000000000)
  directionHi := (4301107777000780321771401283701 / 1000000000000000000000000000000)

def shifts : List ℤ := [18, 19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree075

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree076
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (43011077770007803217714012837 / 10000000000000000000000000000)
  centralHi := (4301107777000780321771401283701 / 1000000000000000000000000000000)
  directionLo := (2165035896496653813092062777547 / 500000000000000000000000000000)
  directionHi := (866014358598661525236825111019 / 200000000000000000000000000000)

def shifts : List ℤ := [19, 20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree076

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree077
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (2165035896496653813092062777547 / 500000000000000000000000000000)
  centralHi := (866014358598661525236825111019 / 200000000000000000000000000000)
  directionLo := (4358843350658057502357208764723 / 1000000000000000000000000000000)
  directionHi := (1089710837664514375589302191181 / 250000000000000000000000000000)

def shifts : List ℤ := [20, 21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree077

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree078
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (4358843350658057502357208764723 / 1000000000000000000000000000000)
  centralHi := (1089710837664514375589302191181 / 250000000000000000000000000000)
  directionLo := (877485247253209273972195581951 / 200000000000000000000000000000)
  directionHi := (1096856559066511592465244477439 / 250000000000000000000000000000)

def shifts : List ℤ := [21, 22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree078

namespace ForestUnimodality.Stage59KernelData.Cell090.Degree079
open FiniteMarginalSupport FiniteKernelCurvatureCertificate
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def witness : DegreeWitness where
  centralLo := (877485247253209273972195581951 / 200000000000000000000000000000)
  centralHi := (1096856559066511592465244477439 / 250000000000000000000000000000)
  directionLo := (4415824113546114627228822281391 / 1000000000000000000000000000000)
  directionHi := (275989007096632164201801392587 / 62500000000000000000000000000)

def shifts : List ℤ := [22]

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
end ForestUnimodality.Stage59KernelData.Cell090.Degree079
