import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell084.Parameters
import ForestUnimodality.BinomialMassData.Q3579_7004.Batch000_049
import ForestUnimodality.BinomialMassData.Q3579_7004.Batch050_099
import ForestUnimodality.BinomialMassData.Q3579_7004.Batch100_149
import ForestUnimodality.BinomialMassData.Q3579_7004.Batch150_199
import ForestUnimodality.BinomialMassData.Q5381_10506.Batch000_049
import ForestUnimodality.BinomialMassData.Q5381_10506.Batch050_099
import ForestUnimodality.BinomialMassData.Q5381_10506.Batch100_149
import ForestUnimodality.BinomialMassData.Q5381_10506.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree000.table
  base := (909412077663110937530888127/10000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (182)
      previous := (91)
      next := (91)
      square := (603664699330803064536432600000000000000)
      linear := (-15642362441633478418318015000000000000)
      constant := (909412077663110937530888127000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree000.table
  base := (909412077663110937530888127/10000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (182)
      previous := (91)
      next := (91)
      square := (603664699330803064536432600000000000000)
      linear := (-15642362441633478418318015000000000000)
      constant := (909412077663110937530888127000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 0 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 0 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree001.table
  base := (516702935271350610826834591993196667893563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-1939491220909689305526935139420715000000000000)
      constant := (1584719503661098228716740490655992623208332051563) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree001.table
  base := (103158165097082570115749257568494654347797/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 91980030000000000000000000000000000000000000000
      center := (1674036546)
      previous := (837018273)
      next := (837018273)
      square := (5552509715438824580015300664097800000000000000)
      linear := (-5831686373835670868655846586794645000000000000)
      constant := (4745775853094602797355093774073981713374999246955) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 1 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 1 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (4998515399417790539/10000000000000000000)
  directionHi := (49985153994177905391/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree002.table
  base := (12295373970947563271201848926591944899661/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-3831022942930967924589828826533415000000000000)
      constant := (944422857916999066965961324616722108857638141525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree002.table
  base := (306415049955447318689253324020832383184833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-3839831417002036559306522938888415000000000000)
      constant := (941460111992158506376999935335598162677081162833) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 2 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 2 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4998515399417790539/10000000000000000000)
  centralHi := (49985153994177905391/100000000000000000000)
  directionLo := (70689682695874076313/100000000000000000000)
  directionHi := (35344841347937038157/50000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree003.table
  base := (38712487523502444243552377625105436675403/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-5722554664952246543652722513646115000000000000)
      constant := (597885672027681339670488225485654633511111367015) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree003.table
  base := (96387740143962682835809225804863758536809/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-5735767376058849495727763682178615000000000000)
      constant := (595493309672081733066605825897033309575229861618) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 3 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 3 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70689682695874076313/100000000000000000000)
  centralHi := (35344841347937038157/50000000000000000000)
  directionLo := (43288413171035266727/50000000000000000000)
  directionHi := (17315365268414106691/20000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree004.table
  base := (1014234130302075356433328698878763655479/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-7614086386973525162715616200758815000000000000)
      constant := (405864800418256082814301112604927530547170493312) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree004.table
  base := (129238511942943528441973854626267454844001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 91980030000000000000000000000000000000000000000
      center := (1674036546)
      previous := (837018273)
      next := (837018273)
      square := (5552509715438824580015300664097800000000000000)
      linear := (-22895110005346987296447013276406445000000000000)
      constant := (1212336600755066164405741366112816658457485730003) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 4 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 4 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43288413171035266727/50000000000000000000)
  centralHi := (17315365268414106691/20000000000000000000)
  directionLo := (99970307988355810781/100000000000000000000)
  directionHi := (49985153994177905391/50000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree005.table
  base := (92649177311801544655647778140146419450261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-9505618108994803781778509887871515000000000000)
      constant := (296267015639321764542516915343836043430919676261) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree005.table
  base := (46114104435948583476077396141744600350737/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-9527639294172475368570245168759015000000000000)
      constant := (295032940230021596590610680339745560339919985474) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 5 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 5 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99970307988355810781/100000000000000000000)
  centralHi := (49985153994177905391/50000000000000000000)
  directionLo := (13971275274597115453/12500000000000000000)
  directionHi := (894161617574215389/800000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree006.table
  base := (6979836687610662171664301954330293816893/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-11397149831016082400841403574984215000000000000)
      constant := (231546999544448176673401265284950354228877548930) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree006.table
  base := (4343278614842050875930854110068259073629/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-11423575253229288304991485912049215000000000000)
      constant := (230690538169364030723066855552812843208089402064) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 6 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 6 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13971275274597115453/12500000000000000000)
  centralHi := (894161617574215389/800000000000000000)
  directionLo := (6121906100008819241/5000000000000000000)
  directionHi := (122438122000176384821/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree007.table
  base := (27433458064739911038680594673757801190801/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-13288681553037361019904297262096915000000000000)
      constant := (192074309002732243306507628233338283167594113602) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree007.table
  base := (54638320991824691439442672802816529172347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 91980030000000000000000000000000000000000000000
      center := (1674036546)
      previous := (837018273)
      next := (837018273)
      square := (5552509715438824580015300664097800000000000000)
      linear := (-39958533636858303724238179966018245000000000000)
      constant := (574452720705849060262014085633938171276835223041) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 7 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 7 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6121906100008819241/5000000000000000000)
  centralHi := (122438122000176384821/100000000000000000000)
  directionLo := (132248286713861650167/100000000000000000000)
  directionHi := (16531035839232706271/12500000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree008.table
  base := (22235571481131647921960028077372225890523/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-15180213275058639638967190949209615000000000000)
      constant := (167474571282280887009343188840377913905138817046) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree008.table
  base := (5536707554655870513322963071544988386671/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-15215447171342914177833967398629615000000000000)
      constant := (167075068261274576502066358405033067508173381368) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 8 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 8 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132248286713861650167/100000000000000000000)
  centralHi := (16531035839232706271/12500000000000000000)
  directionLo := (70689682695874076313/50000000000000000000)
  directionHi := (141379365391748152627/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree009.table
  base := (18397746345461582947489715693823646239931/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-17071744997079918258030084636322315000000000000)
      constant := (152181293907824556994001807587749502640549371862) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree009.table
  base := (36652155571024491684042967327678890444569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-17111383130399727114255208141919815000000000000)
      constant := (151924841473093476993360061247075103281938998569) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 9 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 9 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70689682695874076313/50000000000000000000)
  centralHi := (141379365391748152627/100000000000000000000)
  directionLo := (37488865495633429043/25000000000000000000)
  directionHi := (149955461982533716173/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree010.table
  base := (30843852367290966553124530590778755715807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-18963276719101196877092978323435015000000000000)
      constant := (143140393584165789325064077920273093303419977807) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree010.table
  base := (15362042089953131222674453229409463212229/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 91980030000000000000000000000000000000000000000
      center := (1674036546)
      previous := (837018273)
      next := (837018273)
      square := (5552509715438824580015300664097800000000000000)
      linear := (-57021957268369620152029346655630045000000000000)
      constant := (428997211725569719070536872495290686708943957374) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 10 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 10 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37488865495633429043/25000000000000000000)
  centralHi := (149955461982533716173/100000000000000000000)
  directionLo := (79033467907932513561/50000000000000000000)
  directionHi := (158066935815865027123/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree011.table
  base := (26052121081506866975683437474872695008647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-20854808441122475496155872010547715000000000000)
      constant := (138622336357573432779067061823142391519206710647) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree011.table
  base := (5189888164285474362985093118855091641251/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-20903255048513352987097689628500215000000000000)
      constant := (138580778320961024698902282748009101635836036255) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 11 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 11 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79033467907932513561/50000000000000000000)
  centralHi := (158066935815865027123/100000000000000000000)
  directionLo := (41445500221705668219/25000000000000000000)
  directionHi := (165782000886822672877/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree012.table
  base := (22087082253870656029451755735652945204147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-22746340163143754115218765697660415000000000000)
      constant := (137605479861470060321394947023050370648859906147) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree012.table
  base := (21997508998914686484501929986804952664969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-22799191007570165923518930371790415000000000000)
      constant := (137655987600890508623238717310048301675747618969) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 12 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 12 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41445500221705668219/25000000000000000000)
  centralHi := (165782000886822672877/100000000000000000000)
  directionLo := (43288413171035266727/25000000000000000000)
  directionHi := (173153652684141066909/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree013.table
  base := (9370726613544560398637115226069380951571/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-24637871885165032734281659384773115000000000000)
      constant := (139454295261312023854836804777015147383795275142) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree013.table
  base := (3732496407554476371119577879865963179/2000000000000000000000000000000000000)
  polynomial :=
    { denominator := 91980030000000000000000000000000000000000000000
      center := (1674036546)
      previous := (837018273)
      next := (837018273)
      square := (5552509715438824580015300664097800000000000000)
      linear := (-74085380899880936579820513345241845000000000000)
      constant := (418781084834582655945268174751773067091657685000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 13 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 13 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43288413171035266727/25000000000000000000)
  centralHi := (173153652684141066909/100000000000000000000)
  directionLo := (90112017868986032813/50000000000000000000)
  directionHi := (180224035737972065627/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree014.table
  base := (635147091165457814047691896347201480047/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-26529403607186311353344553071885815000000000000)
      constant := (143750099510811449718455749241289274625639551175) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree014.table
  base := (15808654868847957828631521078808705192491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-26591062925683791796361411858370815000000000000)
      constant := (143977828475145520316636337426989753928882598491) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 14 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 14 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90112017868986032813/50000000000000000000)
  centralHi := (180224035737972065627/100000000000000000000)
  directionLo := (46756830167837185011/25000000000000000000)
  directionHi := (37405464134269748009/20000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree015.table
  base := (1675439850301321371306690875463156964703/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-28420935329207589972407446758998515000000000000)
      constant := (150200900141824818272366110505024886485490901624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree015.table
  base := (6670638626872209718024955291453455885437/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-28486998884740604732782652601661015000000000000)
      constant := (150517883866068988660367351606131836896411454874) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 15 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 15 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46756830167837185011/25000000000000000000)
  centralHi := (37405464134269748009/20000000000000000000)
  directionLo := (96795834488532086743/50000000000000000000)
  directionHi := (193591668977064173487/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree016.table
  base := (2811526686502129277037072907024236709093/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-30312467051228868591470340446111215000000000000)
      constant := (158592472442412540256762423409040207097263388372) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree016.table
  base := (5595377686147510281425346396645706411121/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 91980030000000000000000000000000000000000000000
      center := (1674036546)
      previous := (837018273)
      next := (837018273)
      square := (5552509715438824580015300664097800000000000000)
      linear := (-91148804531392253007611680034853645000000000000)
      constant := (477001459186218679772817202998529315013220382726) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 16 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 16 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96795834488532086743/50000000000000000000)
  centralHi := (193591668977064173487/100000000000000000000)
  directionLo := (199940615976711621563/100000000000000000000)
  directionHi := (49985153994177905391/25000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree017.table
  base := (4676519512274735841475320239002547839893/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1930838)
      previous := (965419)
      next := (965419)
      square := (6404278795200489711667013453400000000000000)
      linear := (-111432521706747914223298388004235000000000000)
      constant := (583948392959844153804454122708582310066849674) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree017.table
  base := (930384949230524985234643678273153048379/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1930838)
      previous := (965419)
      next := (965419)
      square := (6404278795200489711667013453400000000000000)
      linear := (-111691594473544050538495273661735000000000000)
      constant := (585683055332211522817427216943956306902528110) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 17 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 17 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199940615976711621563/100000000000000000000)
  centralHi := (49985153994177905391/25000000000000000000)
  directionLo := (103047034815379998333/50000000000000000000)
  directionHi := (206094069630759996667/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree018.table
  base := (153644733582073596352691561617516720839/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-34095530495271425829596127820336615000000000000)
      constant := (180577725380614491467210785321399501680454741950) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree018.table
  base := (7638581370620205509146737799377718397451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-34174806761911043542046374831531615000000000000)
      constant := (181174928317386527110690769338437178984303163451) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 18 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 18 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103047034815379998333/50000000000000000000)
  centralHi := (206094069630759996667/100000000000000000000)
  directionLo := (212069048087622228939/100000000000000000000)
  directionHi := (10603452404381111447/5000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree019.table
  base := (6199823779929563343778247179836539053773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-35987062217292704448659021507449315000000000000)
      constant := (193938528253607524903973472213469112325407071773) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree019.table
  base := (1232228723593793437000183939464557161653/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 91980030000000000000000000000000000000000000000
      center := (1674036546)
      previous := (837018273)
      next := (837018273)
      square := (5552509715438824580015300664097800000000000000)
      linear := (-108212228162903569435402846724465445000000000000)
      constant := (583903226655679159744935171831150793332778894795) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 19 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 19 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (212069048087622228939/100000000000000000000)
  centralHi := (10603452404381111447/5000000000000000000)
  directionLo := (21788023493793995073/10000000000000000000)
  directionHi := (217880234937939950731/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree020.table
  base := (1219532336573517498101812416312111733641/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-37878593939313983067721915194562015000000000000)
      constant := (208758654929775541770047528560438578549820158564) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree020.table
  base := (302744836270403518542971199467489474673/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-37966678680024669414888856318112015000000000000)
      constant := (209556165260468963545863801179122905149390282768) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 20 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 20 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21788023493793995073/10000000000000000000)
  centralHi := (217880234937939950731/100000000000000000000)
  directionLo := (223540404393553847249/100000000000000000000)
  directionHi := (894161617574215389/400000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree021.table
  base := (230895785731591990870191894863124602671/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-39770125661335261686784808881674715000000000000)
      constant := (224968136793594097802875997101414079568622218736) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree021.table
  base := (1832062826773113279523027327846780483937/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-39862614639081482351310097061402215000000000000)
      constant := (225870363125624249546598495258321341121062651874) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 21 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 21 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223540404393553847249/100000000000000000000)
  centralHi := (894161617574215389/400000000000000000)
  directionLo := (114530375901172248339/50000000000000000000)
  directionHi := (229060751802344496679/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree022.table
  base := (2629493738264818489963132711342431909941/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-41661657383356540305847702568787415000000000000)
      constant := (242508904651045293059488780151155150078311015941) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree022.table
  base := (520573623736592586621621652870354593261/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 91980030000000000000000000000000000000000000000
      center := (1674036546)
      previous := (837018273)
      next := (837018273)
      square := (5552509715438824580015300664097800000000000000)
      linear := (-125275651794414885863194013414077245000000000000)
      constant := (730557162251716769187171346358882215799392288915) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 22 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 22 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114530375901172248339/50000000000000000000)
  centralHi := (229060751802344496679/100000000000000000000)
  directionLo := (117225577025746547391/50000000000000000000)
  directionHi := (234451154051493094783/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree023.table
  base := (208478617730751763795493653798858790529/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-43553189105377818924910596255900115000000000000)
      constant := (261332565036294613721148834517189477554965636232) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree023.table
  base := (82219880235340335758311752905963042491/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-43654486557195108224152578547982615000000000000)
      constant := (262453957293188266277813870490254394384808969820) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 23 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 23 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117225577025746547391/50000000000000000000)
  centralHi := (234451154051493094783/100000000000000000000)
  directionLo := (119860188611459545793/50000000000000000000)
  directionHi := (239720377222919091587/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree024.table
  base := (398073962012061894898754360248591633187/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-45444720827399097543973489943012815000000000000)
      constant := (281398676603820950881865552671937294391885950374) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree024.table
  base := (96944821341609779138970488113808251813/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-45550422516251921160573819291272815000000000000)
      constant := (282634737851963697233303902570556853710935278504) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 24 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 24 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119860188611459545793/50000000000000000000)
  centralHi := (239720377222919091587/100000000000000000000)
  directionLo := (244876244000352769641/100000000000000000000)
  directionHi := (122438122000176384821/50000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree025.table
  base := (10647241238556453702340810092845747/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-47336252549420376163036383630125515000000000000)
      constant := (302673379764310523125029067068961008299007279040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree025.table
  base := (-14659697765211565991706588646451083201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 91980030000000000000000000000000000000000000000
      center := (1674036546)
      previous := (837018273)
      next := (837018273)
      square := (5552509715438824580015300664097800000000000000)
      linear := (-142339075425926202290985180103689045000000000000)
      constant := (912082910695449777698505456256165989497363952397) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 25 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 25 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244876244000352769641/100000000000000000000)
  centralHi := (122438122000176384821/50000000000000000000)
  directionLo := (249925769970889526953/100000000000000000000)
  directionHi := (124962884985444763477/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree026.table
  base := (-719652010325400614825804094452715592341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-49227784271441654782099277317238215000000000000)
      constant := (325128287850349214310138206027154057041166901659) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree026.table
  base := (-183871197055547385979662630644640915643/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-49342294434365547033416300777853215000000000000)
      constant := (326604362640444492283480219669592716231990585428) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 26 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 26 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249925769970889526953/100000000000000000000)
  centralHi := (124962884985444763477/50000000000000000000)
  directionLo := (50975055121250693799/20000000000000000000)
  directionHi := (63718818901563367249/25000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree027.table
  base := (-6903995330673067836496517647096767323/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-51119315993462933401162171004350915000000000000)
      constant := (348739579237285680485549894030690506608182935400) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree027.table
  base := (-6973286821137482545277913578799674839/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-51238230393422359969837541521143415000000000000)
      constant := (350341182195541507277285242501986316128790232200) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 27 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 27 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50975055121250693799/20000000000000000000)
  centralHi := (63718818901563367249/25000000000000000000)
  directionLo := (259730479026211600363/100000000000000000000)
  directionHi := (64932619756552900091/25000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree028.table
  base := (-1986559087283395910083962645844907481163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-53010847715484212020225064691463615000000000000)
      constant := (373487248154993160967846390946421312817846760837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree028.table
  base := (-1998675591781358459797945722395986791137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 91980030000000000000000000000000000000000000000
      center := (1674036546)
      previous := (837018273)
      next := (837018273)
      square := (5552509715438824580015300664097800000000000000)
      linear := (-159402499057437518718776346793300845000000000000)
      constant := (1125654516540958335908831385947799256307161500589) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 28 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 28 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259730479026211600363/100000000000000000000)
  centralHi := (64932619756552900091/25000000000000000000)
  directionLo := (52899314685544660067/20000000000000000000)
  directionHi := (16531035839232706271/6250000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree029.table
  base := (-2542415231446827415686548393271852570629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-54902379437505490639287958378576315000000000000)
      constant := (399354483236556703499442176800282297996598915371) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree029.table
  base := (-255299786093424035800148132231559739491/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-55030102311535985842680023007723815000000000000)
      constant := (401218597165425190736941211958735903571608545090) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 29 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 29 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52899314685544660067/20000000000000000000)
  centralHi := (16531035839232706271/6250000000000000000)
  directionLo := (134589146084322771861/50000000000000000000)
  directionHi := (269178292168645543723/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree030.table
  base := (-763244373590891361492966094223232514309/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-56793911159526769258350852065689015000000000000)
      constant := (426327150230431588870202401873948912051584366764) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree030.table
  base := (-23923527253092971298948065795815992147/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-56926038270592798779101263751014015000000000000)
      constant := (428328392433239308465630336360376008649447149184) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 30 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 30 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134589146084322771861/50000000000000000000)
  centralHi := (269178292168645543723/100000000000000000000)
  directionLo := (273779963829806914273/100000000000000000000)
  directionHi := (136889981914903457137/50000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree031.table
  base := (-3522123482513204583457477437111720475883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-58685442881548047877413745752801715000000000000)
      constant := (454393360391273773610533623717176936659222246117) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree031.table
  base := (-3530173435876976172279655829149724311623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 91980030000000000000000000000000000000000000000
      center := (1674036546)
      previous := (837018273)
      next := (837018273)
      square := (5552509715438824580015300664097800000000000000)
      linear := (-176465922688948835146567513482912645000000000000)
      constant := (1369607197605900063779986572051299855832518711131) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 31 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 31 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273779963829806914273/100000000000000000000)
  centralHi := (136889981914903457137/50000000000000000000)
  directionLo := (139152779539677235359/50000000000000000000)
  directionHi := (278305559079354470719/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree032.table
  base := (-3953116067389849833199500492337393351833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-60576974603569326496476639439914415000000000000)
      constant := (483543109751819460280828795066010939645886670167) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree032.table
  base := (-1980063939664512692531795489358039110207/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-60717910188706424651943745237594415000000000000)
      constant := (485830670824895677907146420443394405460132455586) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 32 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 32 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139152779539677235359/50000000000000000000)
  centralHi := (278305559079354470719/100000000000000000000)
  directionLo := (70689682695874076313/25000000000000000000)
  directionHi := (282758730783496305253/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree033.table
  base := (-4348701840076456157795300502678181214601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-62468506325590605115539533127027115000000000000)
      constant := (513767977261061717882809426223392119967852119399) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree033.table
  base := (-1088701139194003785780943231649423736267/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-62613846147763237588364985980884615000000000000)
      constant := (516204837922515057013814565370843498200726566932) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 33 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 33 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70689682695874076313/25000000000000000000)
  centralHi := (282758730783496305253/100000000000000000000)
  directionLo := (143571424258202771101/50000000000000000000)
  directionHi := (287142848516405542203/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree034.table
  base := (-4711193578231389437314125658049039832733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1930838)
      previous := (965419)
      next := (965419)
      square := (6404278795200489711667013453400000000000000)
      linear := (-222699093590352538874056840187335000000000000)
      constant := (1886023778340440204047810803355685236414535603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree034.table
  base := (-4716501114802614115710598800923913066967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318270000000000000000000000000000000000000000
      center := (5792514)
      previous := (2896257)
      next := (2896257)
      square := (19212836385601469135001040360200000000000000)
      linear := (-669651717371834434513351834507005000000000000)
      constant := (5684960441952580462166881369766839618817641291) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 34 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 34 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143571424258202771101/50000000000000000000)
  centralHi := (287142848516405542203/100000000000000000000)
  directionLo := (291461028396485796619/100000000000000000000)
  directionHi := (14573051419824289831/5000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree035.table
  base := (-50425393751770525346067481992751440817/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-66251569769633162353665320501252515000000000000)
      constant := (577415820933721383041949152364071452720363718300) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree035.table
  base := (-78861751717286741889600286985852448103/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-66405718065876863461207467467465015000000000000)
      constant := (580163793429490279474315929702414934628880249408) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 35 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 35 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291461028396485796619/100000000000000000000)
  centralHi := (14573051419824289831/5000000000000000000)
  directionLo := (59143231800015385803/20000000000000000000)
  directionHi := (36964519875009616127/12500000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree036.table
  base := (-2672190313100150025787253510026137106381/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-68143101491654440972728214188365215000000000000)
      constant := (610827791721473318602920809856817222211397495238) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree036.table
  base := (-5348386864891870562153299709794832413101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-68301654024933676397628708210755215000000000000)
      constant := (613737654981341782636474478509758724026599920899) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 36 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 36 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59143231800015385803/20000000000000000000)
  centralHi := (36964519875009616127/12500000000000000000)
  directionLo := (37488865495633429043/12500000000000000000)
  directionHi := (59982184793013486469/20000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree037.table
  base := (-5618100695933500549755083551994714031543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-70034633213675719591791107875477915000000000000)
      constant := (645292542906296819010689201841019516034575130457) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree037.table
  base := (-224863120318070250430073093958679297911/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 91980030000000000000000000000000000000000000000
      center := (1674036546)
      previous := (837018273)
      next := (837018273)
      square := (5552509715438824580015300664097800000000000000)
      linear := (-210592769951971468002149846862136245000000000000)
      constant := (1945105696252726001524965542560528451044418206675) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 37 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 37 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37488865495633429043/12500000000000000000)
  centralHi := (59982184793013486469/20000000000000000000)
  directionLo := (304047821786971758143/100000000000000000000)
  directionHi := (4750747215421433721/1562500000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree038.table
  base := (-366554111586891788487273939305653919871/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-71926164935696998210854001562590615000000000000)
      constant := (680806498914717940928977264221979094916345506064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree038.table
  base := (-5867882215701961602113101838415507090667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-72093525943047302270471189697335615000000000000)
      constant := (684052978366529744498080425052602061844507887333) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 38 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 38 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (304047821786971758143/100000000000000000000)
  centralHi := (4750747215421433721/1562500000000000000)
  directionLo := (4814518487847983493/1562500000000000000)
  directionHi := (308129183222270943553/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree039.table
  base := (-608565926498492010775109411467505765487/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-73817696657718276829916895249703315000000000000)
      constant := (717366644732063021522679595503380937305110925130) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree039.table
  base := (-3044137214163069666750958223856632023959/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-73989461902104115206892430440625815000000000000)
      constant := (720787904660626995098983607677732807215819364082) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 39 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 39 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4814518487847983493/1562500000000000000)
  centralHi := (308129183222270943553/100000000000000000000)
  directionLo := (312157186643276718491/100000000000000000000)
  directionHi := (78039296660819179623/25000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree040.table
  base := (-6281310530776343245312235895123804197019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-75709228379739555448979788936816015000000000000)
      constant := (754970437429186113451329179475218871208135548981) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree040.table
  base := (-6283576595217319259845477153969862278159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 91980030000000000000000000000000000000000000000
      center := (1674036546)
      previous := (837018273)
      next := (837018273)
      square := (5552509715438824580015300664097800000000000000)
      linear := (-227656193583482784429941013551748045000000000000)
      constant := (2275712472606618320608284330827633044855906683523) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 40 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 40 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312157186643276718491/100000000000000000000)
  centralHi := (78039296660819179623/25000000000000000000)
  directionLo := (79033467907932513561/25000000000000000000)
  directionHi := (63226774326346010849/20000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree041.table
  base := (-3226259633731641731420670270920122402659/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-77600760101760834068042682623928715000000000000)
      constant := (793615731772101178514428124137824263836650206682) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree041.table
  base := (-1290896367055207974602382929511822315319/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-77781333820217741079734911927206215000000000000)
      constant := (797399611888024909892807752282219893847048153405) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 41 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 41 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79033467907932513561/25000000000000000000)
  centralHi := (63226774326346010849/20000000000000000000)
  directionLo := (320061151051933911147/100000000000000000000)
  directionHi := (80015287762983477787/25000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree042.table
  base := (-6599875857089178502470291503291994950211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-79492291823782112687105576311041415000000000000)
      constant := (833300717648872654551162332706311957690658123789) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree042.table
  base := (-3300787375535841403175200611565676068107/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-79677269779274554016156152670496415000000000000)
      constant := (837272475326021077511892338092189206219015739786) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 42 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 42 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (320061151051933911147/100000000000000000000)
  centralHi := (80015287762983477787/25000000000000000000)
  directionLo := (323940821806252962971/100000000000000000000)
  directionHi := (80985205451563240743/25000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree043.table
  base := (-6723878551942933369637512640237879550599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-81383823545803391306168469998154115000000000000)
      constant := (874023867417484506525952592185171534809983915401) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree043.table
  base := (-6725348515323783581515594937618081558987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 91980030000000000000000000000000000000000000000
      center := (1674036546)
      previous := (837018273)
      next := (837018273)
      square := (5552509715438824580015300664097800000000000000)
      linear := (-244719617214994100857732180241359845000000000000)
      constant := (2634563707344430023293259493345726770466192897039) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 43 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 43 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323940821806252962971/100000000000000000000)
  centralHi := (80985205451563240743/25000000000000000000)
  directionLo := (10242955451393444301/3125000000000000000)
  directionHi := (327774574444590217633/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree044.table
  base := (-1364989585928795704924044766622967017283/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-83275355267824669925231363685266815000000000000)
      constant := (915783891586534983028158486143763467510216523585) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree044.table
  base := (-6826219247466170661507749736364218614437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-83469141697388179888998634157076815000000000000)
      constant := (920144617431791463149002989754697579363917543563) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 44 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 44 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10242955451393444301/3125000000000000000)
  centralHi := (327774574444590217633/100000000000000000000)
  directionLo := (331564001773645345753/100000000000000000000)
  directionHi := (165782000886822672877/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree045.table
  base := (-3451719532244259200264307721737816461761/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-85166886989845948544294257372379515000000000000)
      constant := (958579701497876846969659737823376597230848624478) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree045.table
  base := (-6904538114012935372104510051225653456723/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-85365077656444992825419874900367015000000000000)
      constant := (963141543600082073146716230404840582776033825277) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 45 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 45 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331564001773645345753/100000000000000000000)
  centralHi := (165782000886822672877/50000000000000000000)
  directionLo := (167655303295165385437/50000000000000000000)
  directionHi := (2682484852722646167/800000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree046.table
  base := (-1739912944754029618352499079892773984529/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-87058418711867227163357151059492215000000000000)
      constant := (1002410377895303968061329822247965052782640405884) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree046.table
  base := (-6960601516243293569822974244409483004769/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 91980030000000000000000000000000000000000000000
      center := (1674036546)
      previous := (837018273)
      next := (837018273)
      square := (5552509715438824580015300664097800000000000000)
      linear := (-261783040846505417285523346930971645000000000000)
      constant := (3021533316559190081986786818910137837093685723693) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 46 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 46 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167655303295165385437/50000000000000000000)
  centralHi := (2682484852722646167/800000000000000000)
  directionLo := (339015808645846562389/100000000000000000000)
  directionHi := (33901580864584656239/10000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree047.table
  base := (-874229910140302048772125219339836487499/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-88949950433888505782420044746604915000000000000)
      constant := (1047275144443155113382096952695582184665932628008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree047.table
  base := (-699465967004099192212907099019090946219/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-89156949574558618698262356386947415000000000000)
      constant := (1052252536028585542529443912669057223898015997810) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 47 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 47 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (339015808645846562389/100000000000000000000)
  centralHi := (33901580864584656239/10000000000000000000)
  directionLo := (342680950931940382653/100000000000000000000)
  directionHi := (171340475465970191327/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree048.table
  base := (-14012430885963090456883900274077710851/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-90841482155909784401482938433717615000000000000)
      constant := (1093173345409130518741868683375932352226561574500) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree048.table
  base := (-1401384766728063511710941394877342799209/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-91052885533615431634683597130237615000000000000)
      constant := (1098365187408691036174829194071253480501412033955) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 48 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 48 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342680950931940382653/100000000000000000000)
  centralHi := (171340475465970191327/50000000000000000000)
  directionLo := (346307305368282133817/100000000000000000000)
  directionHi := (173153652684141066909/50000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree049.table
  base := (-6996960936963249915556315516436711668891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-92733013877931063020545832120830315000000000000)
      constant := (1140104426851563873823640467500532391836468525109) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree049.table
  base := (-6997572397950041028032150784195677031633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 91980030000000000000000000000000000000000000000
      center := (1674036546)
      previous := (837018273)
      next := (837018273)
      square := (5552509715438824580015300664097800000000000000)
      linear := (-278846464478016733713314513620583445000000000000)
      constant := (3436545538140025480559863698268044002576008571101) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 49 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 49 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (346307305368282133817/100000000000000000000)
  centralHi := (173153652684141066909/50000000000000000000)
  directionLo := (69979215591849067547/20000000000000000000)
  directionHi := (43737009744905667217/12500000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree050.table
  base := (-3483114204657822958923465593950985430969/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-94624545599952341639608725807943015000000000000)
      constant := (1188067920756905810359538767860110556935327230062) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree050.table
  base := (-3483378009862032063840743046304174375847/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-94844757451729057507526078616818015000000000000)
      constant := (1193702050028779794900948055061868085118957444306) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 50 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 50 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69979215591849067547/20000000000000000000)
  centralHi := (43737009744905667217/12500000000000000000)
  directionLo := (70689682695874076313/20000000000000000000)
  directionHi := (176724206739685190783/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree051.table
  base := (-3457073421769025681223329848503967273411/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1930838)
      previous := (965419)
      next := (965419)
      square := (6404278795200489711667013453400000000000000)
      linear := (-333965665473957163524815292370435000000000000)
      constant := (4280496303327399430700540141027946572392765402) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree051.table
  base := (-6914601949021758832184638017934180129243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1930838)
      previous := (965419)
      next := (965419)
      square := (6404278795200489711667013453400000000000000)
      linear := (-334742883774345572470405949342935000000000000)
      constant := (4300779962651196040775304165723708783008861013) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 51 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 51 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70689682695874076313/20000000000000000000)
  centralHi := (176724206739685190783/50000000000000000000)
  directionLo := (44620674967389285099/12500000000000000000)
  directionHi := (356965399739114280793/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree052.table
  base := (-1368165048235200501633327299599335659487/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-98407609043994898877734513182168415000000000000)
      constant := (1287090625366854133447341266077588741343385992565) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree052.table
  base := (-6841217678235374698546452121554138901293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 91980030000000000000000000000000000000000000000
      center := (1674036546)
      previous := (837018273)
      next := (837018273)
      square := (5552509715438824580015300664097800000000000000)
      linear := (-295909888109528050141105680310195245000000000000)
      constant := (3879554782021421839905818097270478955723490282121) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 52 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 52 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44620674967389285099/12500000000000000000)
  centralHi := (356965399739114280793/100000000000000000000)
  directionLo := (360448071475944131253/100000000000000000000)
  directionHi := (180224035737972065627/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree053.table
  base := (-1686588931867859803260169674021635434401/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-100299140766016177496797406869281115000000000000)
      constant := (1338149219416528991437522722543230568195964398396) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree053.table
  base := (-6746694019693008092786927760218885396279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-100532565328899496316789800846688615000000000000)
      constant := (1344480326000925911668263756602094644656123189721) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 53 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 53 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360448071475944131253/100000000000000000000)
  centralHi := (180224035737972065627/50000000000000000000)
  directionLo := (363897413910224166439/100000000000000000000)
  directionHi := (9097435347755604161/2500000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree054.table
  base := (-3315408086130268248194294740192790689741/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-102190672488037456115860300556393815000000000000)
      constant := (1390238975061647426997590934256393549604926808518) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree054.table
  base := (-82888846272963394034185325028811471453/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-102428501287956309253211041589978815000000000000)
      constant := (1396811369938070385691620587165553404977090443760) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 54 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 54 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363897413910224166439/100000000000000000000)
  centralHi := (9097435347755604161/2500000000000000000)
  directionLo := (183657183000264577231/50000000000000000000)
  directionHi := (367314366000529154463/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree055.table
  base := (-6494272402200196020468446511623826230787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-104082204210058734734923194243506515000000000000)
      constant := (1443359690477613552974160972851201755902580827213) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree055.table
  base := (-3247261779849548330693135169701968411879/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 91980030000000000000000000000000000000000000000
      center := (1674036546)
      previous := (837018273)
      next := (837018273)
      square := (5552509715438824580015300664097800000000000000)
      linear := (-312973311741039366568896846999807045000000000000)
      constant := (4350533581102907572693216209477576858383263444726) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 55 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 55 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (183657183000264577231/50000000000000000000)
  centralHi := (367314366000529154463/100000000000000000000)
  directionLo := (37069982342886591599/10000000000000000000)
  directionHi := (370699823428865915991/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree056.table
  base := (-6336780068379561859174270801564503122273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-105973735932080013353986087930619215000000000000)
      constant := (1497511195038132402547529696011568121862607859727) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree056.table
  base := (-6336996383398882062276854625265983554681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-106220373206069935126053523076559215000000000000)
      constant := (1504579629303060234801679520291819809155364499319) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 56 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 56 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37069982342886591599/10000000000000000000)
  centralHi := (370699823428865915991/100000000000000000000)
  directionLo := (46756830167837185011/12500000000000000000)
  directionHi := (374054641342697480089/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree057.table
  base := (-1231677244653106514881374938599221821401/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-107865267654101291973048981617731915000000000000)
      constant := (1552693344480293412260010651193690772731813562995) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree057.table
  base := (-6158572478319258620640654756282080088229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-108116309165126748062474763819849415000000000000)
      constant := (1560016534771993452495824366631025203667409797771) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 57 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 57 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46756830167837185011/12500000000000000000)
  centralHi := (374054641342697480089/100000000000000000000)
  directionLo := (75475927375511120989/20000000000000000000)
  directionHi := (188689818438777802473/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree058.table
  base := (-5959130652432087409183420866265798724817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-109756799376122570592111875304844615000000000000)
      constant := (1608906016821486976178533974602462652343912353183) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree058.table
  base := (-2979645491068826035994479971252536212207/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 91980030000000000000000000000000000000000000000
      center := (1674036546)
      previous := (837018273)
      next := (837018273)
      square := (5552509715438824580015300664097800000000000000)
      linear := (-330036735372550682996688013689418845000000000000)
      constant := (4849465370334832156993009781842491701325022754758) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 58 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 58 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75475927375511120989/20000000000000000000)
  centralHi := (188689818438777802473/50000000000000000000)
  directionLo := (76135118296265201431/20000000000000000000)
  directionHi := (95168897870331501789/25000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree059.table
  base := (-5739046999373770554964810125680824119079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-111648331098143849211174768991957315000000000000)
      constant := (1666149108910725178317536352910976921320079666921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree059.table
  base := (-5739184976773358185108330267483775109801/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-111908181083240373935317245306429815000000000000)
      constant := (1673995293892714391560820840238515150529575024199) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 59 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 59 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76135118296265201431/20000000000000000000)
  centralHi := (95168897870331501789/25000000000000000000)
  directionLo := (19197162652946859709/5000000000000000000)
  directionHi := (383943253058937194181/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree060.table
  base := (-1374540928921854915467921737790445442487/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-113539862820165127830237662679070015000000000000)
      constant := (1724422533515383662844910240023152550931557662052) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree060.table
  base := (-343642651707400913952338126912147459181/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-113804117042297186871738486049720015000000000000)
      constant := (1732536960374304317617749758843547313648057517104) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 60 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 60 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19197162652946859709/5000000000000000000)
  centralHi := (383943253058937194181/100000000000000000000)
  directionLo := (96795834488532086743/25000000000000000000)
  directionHi := (387183337954128346973/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree061.table
  base := (-2618252431920928399040675565785286122513/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-115431394542186406449300556366182715000000000000)
      constant := (1783726216859908958830801966609039165176178038974) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree061.table
  base := (-2618303487489391464240084450286522891087/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 91980030000000000000000000000000000000000000000
      center := (1674036546)
      previous := (837018273)
      next := (837018273)
      square := (5552509715438824580015300664097800000000000000)
      linear := (-347100159004061999424479180379030645000000000000)
      constant := (5376340151217258133623213109962836405676426201478) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 61 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 61 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96795834488532086743/25000000000000000000)
  centralHi := (387183337954128346973/100000000000000000000)
  directionLo := (19519826639158609849/5000000000000000000)
  directionHi := (390396532783172196981/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree062.table
  base := (-2477045397745403744047835568402681357603/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-117322926264207685068363450053295415000000000000)
      constant := (1844060096546110392163363279438060513609815688794) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree062.table
  base := (-990835721361857925507998414084672901861/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-117595988960410812744580967536300415000000000000)
      constant := (1852724502706729487145085567965575598991106360695) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 62 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 62 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19519826639158609849/5000000000000000000)
  centralHi := (390396532783172196981/100000000000000000000)
  directionLo := (393583496133849752841/100000000000000000000)
  directionHi := (196791748066924876421/50000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree063.table
  base := (-1162734681173084040640244867009740300673/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-119214457986228963687426343740408115000000000000)
      constant := (1905424119795668723240168092415288265663585125308) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree063.table
  base := (-145344194420407522792641469668882191553/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-119491924919467625681002208279590615000000000000)
      constant := (1914370265465977983763253856627722383518121934304) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 63 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 63 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393583496133849752841/100000000000000000000)
  centralHi := (196791748066924876421/50000000000000000000)
  directionLo := (198372430070792475251/50000000000000000000)
  directionHi := (396744860141584950503/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree064.table
  base := (-4327063212371664629955111177948880965597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-121105989708250242306489237427520815000000000000)
      constant := (1967818241964772661071201554791378113010598632403) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree064.table
  base := (-4327128107086992623727458043237762513561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 91980030000000000000000000000000000000000000000
      center := (1674036546)
      previous := (837018273)
      next := (837018273)
      square := (5552509715438824580015300664097800000000000000)
      linear := (-364163582635573315852270347068642445000000000000)
      constant := (5931151884627800093782720190724992610686978381317) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 64 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 64 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198372430070792475251/50000000000000000000)
  centralHi := (396744860141584950503/100000000000000000000)
  directionLo := (199940615976711621563/50000000000000000000)
  directionHi := (399881231953423243127/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree065.table
  base := (-1991238287906813915910009523214245681263/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-122997521430271520925552131114633515000000000000)
      constant := (2031242425288614584440861097801224205304003921474) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree065.table
  base := (-1991266172620200193282892641151249233851/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-123283796837581251553844689766171015000000000000)
      constant := (2040765553894614852045966270348020294895527200298) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 65 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 65 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199940615976711621563/50000000000000000000)
  centralHi := (399881231953423243127/100000000000000000000)
  directionLo := (16119727803578280599/4000000000000000000)
  directionHi := (6296768673272765859/1562500000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree066.table
  base := (-1808594617410426387252306459365114918597/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-124889053152292799544615024801746215000000000000)
      constant := (2095696637820069219145053957510372724088933358806) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree066.table
  base := (-723447430403345725803275037096712889437/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-125179732796638064490265930509461215000000000000)
      constant := (2105515011199439007517222233308302420921366342815) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 66 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 66 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16119727803578280599/4000000000000000000)
  centralHi := (6296768673272765859/1562500000000000000)
  directionLo := (203040655355171936177/50000000000000000000)
  directionHi := (81216262142068774471/20000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree067.table
  base := (-3231210004360705688276709505748654559619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-126780584874314078163677918488858915000000000000)
      constant := (2161180852532437805354412777615404243121553586381) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree067.table
  base := (-646250233289822061908644494466223145387/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 91980030000000000000000000000000000000000000000
      center := (1674036546)
      previous := (837018273)
      next := (837018273)
      square := (5552509715438824580015300664097800000000000000)
      linear := (-381227006267084632280061513758254245000000000000)
      constant := (6513896920909364818972673158545125258050304689195) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 67 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 67 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (203040655355171936177/50000000000000000000)
  centralHi := (81216262142068774471/20000000000000000000)
  directionLo := (409146118798715381857/100000000000000000000)
  directionHi := (204573059399357690929/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree068.table
  base := (-2824546341994923265837842686368002000013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1930838)
      previous := (965419)
      next := (965419)
      square := (6404278795200489711667013453400000000000000)
      linear := (-445232237357561788175573744553535000000000000)
      constant := (7708287358341967476842138278692476866781862083) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree068.table
  base := (-112983267768059430791763527456432671101/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1930838)
      previous := (965419)
      next := (965419)
      square := (6404278795200489711667013453400000000000000)
      linear := (-446268528424746333436361287183535000000000000)
      constant := (7744350930126261943652388761110397644807237275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 68 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 68 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (409146118798715381857/100000000000000000000)
  centralHi := (204573059399357690929/50000000000000000000)
  directionLo := (103047034815379998333/25000000000000000000)
  directionHi := (412188139261519993333/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree069.table
  base := (-299650569636985247353643050229720559893/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-130563648318356635401803705863084315000000000000)
      constant := (2295239200560699589869521330117534553519180016856) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree069.table
  base := (-239723491354752638878253991376526312763/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-130867540673808503299529652739331815000000000000)
      constant := (2305970327766950038969443153413517736985423292370) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 69 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 69 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103047034815379998333/25000000000000000000)
  centralHi := (412188139261519993333/100000000000000000000)
  directionLo := (103801968239918227719/25000000000000000000)
  directionHi := (415207872959672910877/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree070.table
  base := (-974594993882514728943252026689690443633/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-132455180040377914020866599550197015000000000000)
      constant := (2363813298165426396003865612801596127320261556734) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree070.table
  base := (-974608024739913427925766121101276748181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 91980030000000000000000000000000000000000000000
      center := (1674036546)
      previous := (837018273)
      next := (837018273)
      square := (5552509715438824580015300664097800000000000000)
      linear := (-398290429898595948707852680447866045000000000000)
      constant := (7124573053494010293327437807291117961332801834914) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 70 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 70 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103801968239918227719/25000000000000000000)
  centralHi := (415207872959672910877/100000000000000000000)
  directionLo := (41820580267078738683/10000000000000000000)
  directionHi := (418205802670787386831/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree071.table
  base := (-740253575225218131450425540614807318027/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-134346711762399192639929493237309715000000000000)
      constant := (2433417325527574718425714661039615179046243799946) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree071.table
  base := (-1480529520891080651027865407029644525653/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-134659412591922129172372134225912215000000000000)
      constant := (2444779475451320461032193049463218305354703376347) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 71 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 71 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41820580267078738683/10000000000000000000)
  centralHi := (418205802670787386831/100000000000000000000)
  directionLo := (21059119699511375707/5000000000000000000)
  directionHi := (421182393990227514141/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree072.table
  base := (-30973745827658441501457602384944759781/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-136238243484420471258992386924422415000000000000)
      constant := (2504051270930933856729121853070143253410134215008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree072.table
  base := (-247794766250120871045972024611108684827/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-136555348550978942108793374969202415000000000000)
      constant := (2515735689168583337472920163555559244644846932692) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 72 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 72 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21059119699511375707/5000000000000000000)
  centralHi := (421182393990227514141/100000000000000000000)
  directionLo := (424138096175244457879/100000000000000000000)
  directionHi := (10603452404381111447/2500000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree073.table
  base := (-481151369112804849436353425457491464129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-138129775206441749878055280611535115000000000000)
      constant := (2575715124462374860611332551216341181963489021871) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree073.table
  base := (-481167842550091787542838756216052699799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 91980030000000000000000000000000000000000000000
      center := (1674036546)
      previous := (837018273)
      next := (837018273)
      square := (5552509715438824580015300664097800000000000000)
      linear := (-415353853530107265135643847137477845000000000000)
      constant := (7763178947876861264004223190283474651119090698603) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 73 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 73 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (424138096175244457879/100000000000000000000)
  centralHi := (10603452404381111447/2500000000000000000)
  directionLo := (427073342936529576179/100000000000000000000)
  directionHi := (21353667146826478809/5000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree074.table
  base := (49515605983550210922589248832857278523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-140021306928463028497118174298647815000000000000)
      constant := (2648408877734291500885622615474534186748808796523) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree074.table
  base := (49501473251516923735239957518767098079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-140347220469092567981635856455782815000000000000)
      constant := (2660751347626371540747597543117861332441477312079) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 74 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 74 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (427073342936529576179/100000000000000000000)
  centralHi := (21353667146826478809/5000000000000000000)
  directionLo := (85997710636226654437/20000000000000000000)
  directionHi := (214994276590566636093/50000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree075.table
  base := (600838744104701806105233233753904404691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-141912838650484307116181067985760515000000000000)
      constant := (2722132523649813429757626897581529298408687010691) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree075.table
  base := (600826621523023163121881611689171951883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-142243156428149380918057097199073015000000000000)
      constant := (2734810777238972309284473838019538925393645229883) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 75 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 75 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85997710636226654437/20000000000000000000)
  centralHi := (214994276590566636093/50000000000000000000)
  directionLo := (54110516463794083409/12500000000000000000)
  directionHi := (432884131710352667273/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree076.table
  base := (293204021688644376616192779069421122383/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-143804370372505585735243961672873215000000000000)
      constant := (2796886056204189730661975856362175361922589601532) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree076.table
  base := (1172805690116469507930678437897224192489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 91980030000000000000000000000000000000000000000
      center := (1674036546)
      previous := (837018273)
      next := (837018273)
      square := (5552509715438824580015300664097800000000000000)
      linear := (-432417277161618581563435013827089645000000000000)
      constant := (8429713796802325532018367997685625451814186399467) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 76 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 76 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54110516463794083409/12500000000000000000)
  centralHi := (432884131710352667273/100000000000000000000)
  directionLo := (435760469875879901461/100000000000000000000)
  directionHi := (217880234937939950731/50000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree077.table
  base := (14123567814696964015522673698277013367/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-145695902094526864354306855359985915000000000000)
      constant := (2872669470316762236322966058370093088907529420875) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree077.table
  base := (882718530920011243278975383947627551869/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-146035028346263006790899578685653415000000000000)
      constant := (2886032807753468366296773673278342987543315811738) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 77 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 77 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435760469875879901461/100000000000000000000)
  centralHi := (217880234937939950731/50000000000000000000)
  directionLo := (342670270466579849/78125000000000000)
  directionHi := (438617946197222206721/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree078.table
  base := (95149080491656426153593187018197622179/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-147587433816548142973369749047098615000000000000)
      constant := (2949482761688810763534447408246373155694960904475) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree078.table
  base := (237871936897995578011160534212427763979/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-147930964305319819727320819428943615000000000000)
      constant := (2963195399503640223548977383343041322367873779790) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 78 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 78 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342670270466579849/78125000000000000)
  centralHi := (438617946197222206721/100000000000000000000)
  directionLo := (441456926943151492193/100000000000000000000)
  directionHi := (220728463471575746097/50000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree079.table
  base := (1506329003432062663826133435427526453583/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-149478965538569421592432642734211315000000000000)
      constant := (3027325926683281438845686574193318591818423863166) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree079.table
  base := (376581431854927934331308841166150849349/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 91980030000000000000000000000000000000000000000
      center := (1674036546)
      previous := (837018273)
      next := (837018273)
      square := (5552509715438824580015300664097800000000000000)
      linear := (-449480700793129897991226180516701445000000000000)
      constant := (9124177111914571188481232751619711899586117200376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 79 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 79 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (441456926943151492193/100000000000000000000)
  centralHi := (220728463471575746097/50000000000000000000)
  directionLo := (444277766679712066469/100000000000000000000)
  directionHi := (44427776667971206647/10000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree080.table
  base := (733447591383859028794224948542914081299/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-151370497260590700211495536421324015000000000000)
      constant := (3106198962223025376503453783247416315580884076495) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree080.table
  base := (366723234121011086143702038776723299291/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-151722836223433445600163300915524015000000000000)
      constant := (3120623718157931213025770309754420924123495052910) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 80 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 80 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444277766679712066469/100000000000000000000)
  centralHi := (44427776667971206647/10000000000000000000)
  directionLo := (447080808787107694499/100000000000000000000)
  directionHi := (894161617574215389/200000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree081.table
  base := (4342466013355141073767752754284054276639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-153262028982611978830558430108436715000000000000)
      constant := (3186101865704695672902968163834342010946229450639) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree081.table
  base := (4342461200860565978277354070173471912111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-153618772182490258536584541658814215000000000000)
      constant := (3200889439526570215197517100634577812556004238111) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 81 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 81 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (447080808787107694499/100000000000000000000)
  centralHi := (894161617574215389/200000000000000000)
  directionLo := (112466596486900287129/25000000000000000000)
  directionHi := (449866385947601148517/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree082.table
  base := (5038341457841331975859734802010012489473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-155153560704633257449621323795549415000000000000)
      constant := (3267034634925890814435033286998184567802736707473) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree082.table
  base := (1007667466853344416348908577759717203121/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 91980030000000000000000000000000000000000000000
      center := (1674036546)
      previous := (837018273)
      next := (837018273)
      square := (5552509715438824580015300664097800000000000000)
      linear := (-466544124424641214419017347206313245000000000000)
      constant := (9846568597798097743548712747350818825567292836815) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 82 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 82 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112466596486900287129/25000000000000000000)
  centralHi := (449866385947601148517/100000000000000000000)
  directionLo := (113158705151597183561/25000000000000000000)
  directionHi := (90526964121277746849/20000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree083.table
  base := (575486368271135395944880248118768631289/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-157045092426654536068684217482662115000000000000)
      constant := (3348997268023504661843947771011850791173007052890) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree083.table
  base := (5754860149929864669745083747000545422351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-157410644100603884409427023145394615000000000000)
      constant := (3364523995562782660819798572613698751765473588351) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 83 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 83 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113158705151597183561/25000000000000000000)
  centralHi := (90526964121277746849/20000000000000000000)
  directionLo := (455386425407257161607/100000000000000000000)
  directionHi := (56923303175907145201/12500000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree084.table
  base := (1298406434789455546477468349755733548349/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-158936624148675814687747111169774815000000000000)
      constant := (3431989763421557729902057739071770879074857911745) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree084.table
  base := (6492029147728490129098350882558257818257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-159306580059660697345848263888684815000000000000)
      constant := (3447892826883447423908684659357259611029033780257) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 84 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 84 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (455386425407257161607/100000000000000000000)
  centralHi := (56923303175907145201/12500000000000000000)
  directionLo := (458121503604688993357/100000000000000000000)
  directionHi := (229060751802344496679/50000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree085.table
  base := (7249846496780954369664147164612280725563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1930838)
      previous := (965419)
      next := (965419)
      square := (6404278795200489711667013453400000000000000)
      linear := (-556498809241166412826332196736635000000000000)
      constant := (12166131902377337159990068893727252936217497867) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree085.table
  base := (362492195241801385048940915497096282247/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318270000000000000000000000000000000000000000
      center := (5792514)
      previous := (2896257)
      next := (2896257)
      square := (19212836385601469135001040360200000000000000)
      linear := (-1673382519225441283206949875072405000000000000)
      constant := (36667432788217718148890304718170884167501505380) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 85 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 85 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (458121503604688993357/100000000000000000000)
  centralHi := (229060751802344496679/50000000000000000000)
  directionLo := (46084034945395433521/10000000000000000000)
  directionHi := (460840349453954335211/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree086.table
  base := (8028306283509018635365095128203627239821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-162719687592718371925872898544000215000000000000)
      constant := (3601064335992603904332486345784856151820918425821) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree086.table
  base := (8028304063808684360911333813508799857093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-163098451977774323218690745375265215000000000000)
      constant := (3617733589611437907266208816924992558870646995093) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 86 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 86 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46084034945395433521/10000000000000000000)
  centralHi := (460840349453954335211/100000000000000000000)
  directionLo := (463543248580609174157/100000000000000000000)
  directionHi := (231771624290304587079/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree087.table
  base := (8827411223181105586766902874165421766993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-164611219314739650544935792231112915000000000000)
      constant := (3687146411084843995323372517882850856053022304993) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree087.table
  base := (4413704661254388396902825948101514040343/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-164994387936831136155111986118555415000000000000)
      constant := (3704205518996486161496263038796633022798411356686) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 87 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 87 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463543248580609174157/100000000000000000000)
  centralHi := (231771624290304587079/50000000000000000000)
  directionLo := (233115239165356856213/50000000000000000000)
  directionHi := (466230478330713712427/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree088.table
  base := (9647161052873142218775881142687108112267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-166502751036760929163998685918225615000000000000)
      constant := (3774258344257645241452098170216891786159318734267) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree088.table
  base := (4823579712790284897906498297667592677417/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 91980030000000000000000000000000000000000000000
      center := (1674036546)
      previous := (837018273)
      next := (837018273)
      square := (5552509715438824580015300664097800000000000000)
      linear := (-500670971687663847274599680585536845000000000000)
      constant := (11375135437911592014627579407545004480899319196502) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 88 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 88 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233115239165356856213/50000000000000000000)
  centralHi := (466230478330713712427/100000000000000000000)
  directionLo := (93780461620597237913/20000000000000000000)
  directionHi := (234451154051493094783/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree089.table
  base := (5243777775150970579180909519159737856781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-168394282758782207783061579605338315000000000000)
      constant := (3862400134829487167949765303151320767107256805562) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree089.table
  base := (5243777078619655222867607321224908594751/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-168786259854944762027954467605135815000000000000)
      constant := (3880252469871975169163852648960860279452830321502) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 89 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 89 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93780461620597237913/20000000000000000000)
  centralHi := (234451154051493094783/50000000000000000000)
  directionLo := (471558999664018147533/100000000000000000000)
  directionHi := (235779499832009073767/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree090.table
  base := (11348594527574848251027403117963225153777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-170285814480803486402124473292451015000000000000)
      constant := (3951571782224290709286030999172281903784705435777) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree090.table
  base := (2837148333792767257712052324480029351401/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-170682195814001574964375708348426015000000000000)
      constant := (3969827490141844963547099784806416852885699269604) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 90 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 90 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471558999664018147533/100000000000000000000)
  centralHi := (235779499832009073767/50000000000000000000)
  directionLo := (237100403723797540683/50000000000000000000)
  directionHi := (474200807447595081367/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree091.table
  base := (3057569456474984230777856752175302570589/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-172177346202824765021187366979563715000000000000)
      constant := (4041773285955199659794123425879204853176913778356) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree091.table
  base := (12230276805372215712855656104128137655971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 91980030000000000000000000000000000000000000000
      center := (1674036546)
      previous := (837018273)
      next := (837018273)
      square := (5552509715438824580015300664097800000000000000)
      linear := (-517734395319175163702390847275148645000000000000)
      constant := (12181310618923894314813264522904870380044034225913) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 91 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 91 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (237100403723797540683/50000000000000000000)
  centralHi := (474200807447595081367/100000000000000000000)
  directionLo := (119206994709772805501/25000000000000000000)
  directionHi := (95365595767818244401/20000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree092.table
  base := (13132605311109092470498515588768366048807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-174068877924846043640250260666676415000000000000)
      constant := (4133004645610854445623110139033382804074008310807) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree092.table
  base := (6566302218891879441202873960043200736329/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-174474067732115200837218189835006415000000000000)
      constant := (4152080617971573595002553567400405357001570900658) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 92 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 92 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119206994709772805501/25000000000000000000)
  centralHi := (95365595767818244401/20000000000000000000)
  directionLo := (479440754445838183173/100000000000000000000)
  directionHi := (239720377222919091587/50000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree093.table
  base := (14055576869869043734167920743510394400961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-175960409646867322259313154353789115000000000000)
      constant := (4225265860843775144066162365894537563993740826961) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree093.table
  base := (878473507662380799501860777816936209789/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-176370003691172013773639430578296615000000000000)
      constant := (4244758724796001204712151144720030675278388540624) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 93 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 93 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (479440754445838183173/100000000000000000000)
  centralHi := (239720377222919091587/50000000000000000000)
  directionLo := (482039368354303801269/100000000000000000000)
  directionHi := (48203936835430380127/10000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree094.table
  base := (14999192406474616047361760603610778847207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-177851941368888600878376048040901815000000000000)
      constant := (4318556931360529593889825773893462824056315509207) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree094.table
  base := (14999191767134578501255672707860727176481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 91980030000000000000000000000000000000000000000
      center := (1674036546)
      previous := (837018273)
      next := (837018273)
      square := (5552509715438824580015300664097800000000000000)
      linear := (-534797818950686480130182013964760445000000000000)
      constant := (13015413579491266007183263917344035247151453767443) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 94 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 94 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (482039368354303801269/100000000000000000000)
  centralHi := (48203936835430380127/10000000000000000000)
  directionLo := (121156012093714798559/25000000000000000000)
  directionHi := (484624048374859194237/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree095.table
  base := (7981725920067368655506588112064925869097/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-179743473090909879497438941728014515000000000000)
      constant := (4412877856913412287247289274438114618309154542194) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree095.table
  base := (3990862823299086478212296842103514551369/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-180161875609285639646481912064877015000000000000)
      constant := (4433218022835084306134373708081519733372047621476) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 95 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 95 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121156012093714798559/25000000000000000000)
  centralHi := (484624048374859194237/100000000000000000000)
  directionLo := (487195016274858402651/100000000000000000000)
  directionHi := (121798754068714600663/25000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree096.table
  base := (1059272193917217791078569004059395225393/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-181635004812931158116501835415127215000000000000)
      constant := (4508228637293401908451755714849429797127202614288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree096.table
  base := (16948354634834205764492918860409915111807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-182057811568342452582903152808167215000000000000)
      constant := (4528999213607787835704553948364816700142715373807) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 96 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 96 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (487195016274858402651/100000000000000000000)
  centralHi := (121798754068714600663/25000000000000000000)
  directionLo := (489752488000705539283/100000000000000000000)
  directionHi := (122438122000176384821/25000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree097.table
  base := (2244237767074512255121636040166335032433/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-183526536534952436735564729102239915000000000000)
      constant := (4604609272324201069704125732509615073256196883464) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree097.table
  base := (897695086822748962285601442760319513437/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 91980030000000000000000000000000000000000000000
      center := (1674036546)
      previous := (837018273)
      next := (837018273)
      square := (5552509715438824580015300664097800000000000000)
      linear := (-551861242582197796557973180654372245000000000000)
      constant := (13877444295934251547836602085522344695811041326220) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 97 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 97 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489752488000705539283/100000000000000000000)
  centralHi := (122438122000176384821/25000000000000000000)
  directionLo := (492296673889538789201/100000000000000000000)
  directionHi := (246148336944769394601/50000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree098.table
  base := (9490046446711867684141645556270104472567/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-185418068256973715354627622789352615000000000000)
      constant := (4702019761857191988671727782598512200665989789134) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree098.table
  base := (4745023137805302740999157601522056992801/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-185849683486456078455745634294747615000000000000)
      constant := (4723664677802368661786423242620898408047939435204) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 98 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 98 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (492296673889538789201/100000000000000000000)
  centralHi := (246148336944769394601/50000000000000000000)
  directionLo := (30926736179444908387/6250000000000000000)
  directionHi := (494827778871118534193/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree099.table
  base := (20026927332321077218028741076087693663337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-187309599978994993973690516476465315000000000000)
      constant := (4800460105767167403171969037759751748609484905337) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree099.table
  base := (20026927039697400089378030881688171168249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-187745619445512891392166875038037815000000000000)
      constant := (4822548950959732988247036749128702586990022602249) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 99 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 99 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30926736179444908387/6250000000000000000)
  centralHi := (494827778871118534193/100000000000000000000)
  directionLo := (49734600266046801863/10000000000000000000)
  directionHi := (497346002660468018631/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree100.table
  base := (21094405418907941085882552863910215467099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-189201131701016272592753410163578015000000000000)
      constant := (4899930303948717639266400763189287459532341001099) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree100.table
  base := (10547202584352397223063406098992790336639/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 91980030000000000000000000000000000000000000000
      center := (1674036546)
      previous := (837018273)
      next := (837018273)
      square := (5552509715438824580015300664097800000000000000)
      linear := (-568924666213709112985764347343984045000000000000)
      constant := (14767402754045352223933507929367506214989553063834) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 100 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 100 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49734600266046801863/10000000000000000000)
  centralHi := (497346002660468018631/100000000000000000000)
  directionLo := (499851539941779053907/100000000000000000000)
  directionHi := (124962884985444763477/25000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree101.table
  base := (2772815890533004082941822860286751268071/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-191092663423037551211816303850690715000000000000)
      constant := (5000430356313173045685449750318649338647255632568) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree101.table
  base := (22182526910352637365920362266371025018379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-191537491363626517265009356524618215000000000000)
      constant := (5023420578883008833142987127616008256577375032379) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 101 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 101 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499851539941779053907/100000000000000000000)
  centralHi := (124962884985444763477/25000000000000000000)
  directionLo := (31396536284003876631/6250000000000000000)
  directionHi := (502344580544062026097/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree102.table
  base := (2329129242408501183026391482711419618567/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1930838)
      previous := (965419)
      next := (965419)
      square := (6404278795200489711667013453400000000000000)
      linear := (-667765381124771037477090648919735000000000000)
      constant := (17653841739744001700050676640271537007333773030) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree102.table
  base := (23291292241218701528164944626227841440663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1930838)
      previous := (965419)
      next := (965419)
      square := (6404278795200489711667013453400000000000000)
      linear := (-669319817725547855368271962864735000000000000)
      constant := (17734975548413822461437102027775896169843993767) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 102 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 102 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31396536284003876631/6250000000000000000)
  centralHi := (502344580544062026097/100000000000000000000)
  directionLo := (504825309608988701001/100000000000000000000)
  directionHi := (252412654804494350501/50000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree103.table
  base := (24420701297968324940235630401163754649739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (52598)
      previous := (26299)
      next := (26299)
      square := (174459098106602085651029021400000000000000)
      linear := (-18368906293437657503057978247235000000000000)
      constant := (490575928297171620913686931286135075093774571) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree103.table
  base := (24420701141656126681457320551311336315059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (157794)
      previous := (78897)
      next := (78897)
      square := (523377294319806256953087064200000000000000)
      linear := (-55234997628920768160387926669205000000000000)
      constant := (1478488919346018764097609427001114428585156153) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 103 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 103 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504825309608988701001/100000000000000000000)
  centralHi := (252412654804494350501/50000000000000000000)
  directionLo := (507293907751347807471/100000000000000000000)
  directionHi := (31705869234459237967/6250000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree104.table
  base := (25570753728808872050041674767831826143671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-196767258589101387069004984912028815000000000000)
      constant := (5308109637816760497029838025709944056788321429671) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree104.table
  base := (25570753595207116512896460951357095080419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-197225299240796956074273078754488815000000000000)
      constant := (5332485723699678207435407212497349464873659734419) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 104 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 104 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (507293907751347807471/100000000000000000000)
  centralHi := (31705869234459237967/6250000000000000000)
  directionLo := (50975055121250693799/10000000000000000000)
  directionHi := (509750551212506937991/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree105.table
  base := (106965798809150555885407057657222380531/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-198658790311122665688067878599141515000000000000)
      constant := (5412729106278314691763810826543917725232606632750) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree105.table
  base := (1069657983524281733144385592053250970629/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-199121235199853769010694319497779015000000000000)
      constant := (5437576159206513883075964240598979625729987115725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 105 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 105 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50975055121250693799/10000000000000000000)
  centralHi := (509750551212506937991/100000000000000000000)
  directionLo := (512195412007249766147/100000000000000000000)
  directionHi := (128048853001812441537/25000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree106.table
  base := (27932789206439014923301457809344965329021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-200550322033143944307130772286254215000000000000)
      constant := (5518378428652669735855481897917304350543743715021) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree106.table
  base := (13966394554432520811539974081038976095473/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 91980030000000000000000000000000000000000000000
      center := (1674036546)
      previous := (837018273)
      next := (837018273)
      square := (5552509715438824580015300664097800000000000000)
      linear := (-603051513476731745841346680723207645000000000000)
      constant := (16631102864797741133684210618996411435486177880838) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 106 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 106 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (512195412007249766147/100000000000000000000)
  centralHi := (128048853001812441537/25000000000000000000)
  directionLo := (12865716451608369751/2500000000000000000)
  directionHi := (514628658064334790041/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree107.table
  base := (7286193057821177353228542157526002392509/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-202441853755165222926193665973366915000000000000)
      constant := (5625057604909232180675094533187671997195739946036) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree107.table
  base := (29144772147909314082570563875784566020607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-202913107117967394883536800984359415000000000000)
      constant := (5650860110848530551756010699224146547703747082607) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 107 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 107 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12865716451608369751/2500000000000000000)
  centralHi := (514628658064334790041/100000000000000000000)
  directionLo := (517050453361100628999/100000000000000000000)
  directionHi := (517050453361100629/100000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree108.table
  base := (30377398768524037975768155513619393618063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-204333385477186501545256559660479615000000000000)
      constant := (5732766635022552119354047208914433719452374776063) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree108.table
  base := (30377398697287186168881593282720801391139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-204809043077024207819958041727649615000000000000)
      constant := (5759053626929981496572990307114381029786033565139) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 108 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 108 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (517050453361100628999/100000000000000000000)
  centralHi := (517050453361100629/100000000000000000)
  directionLo := (259730479026211600363/50000000000000000000)
  directionHi := (519460958052423200727/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree109.table
  base := (3953833601408989667002267321289671401829/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-206224917199207780164319453347592315000000000000)
      constant := (5841505518971519879683515021110876521711432926632) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree109.table
  base := (15815334375205739489638143146002153421237/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 91980030000000000000000000000000000000000000000
      center := (1674036546)
      previous := (837018273)
      next := (837018273)
      square := (5552509715438824580015300664097800000000000000)
      linear := (-620114937108243062269137847412819445000000000000)
      constant := (17604844509470210745728117754462335632849996379422) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 109 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 109 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259730479026211600363/50000000000000000000)
  centralHi := (519460958052423200727/100000000000000000000)
  directionLo := (104372065718862354143/20000000000000000000)
  directionHi := (130465082148577942679/25000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree110.table
  base := (32904582353837240203869374466928935422619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-208116448921229058783382347034705015000000000000)
      constant := (5951274256738686521021879996922454295434685276619) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree110.table
  base := (32904582301846067557962842332398127307831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-208600914995137833692800523214230015000000000000)
      constant := (5978543739512129643214574916000126015723937153831) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 110 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 110 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104372065718862354143/20000000000000000000)
  centralHi := (130465082148577942679/25000000000000000000)
  directionLo := (262124358931206894693/50000000000000000000)
  directionHi := (524248717862413789387/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree111.table
  base := (53436155299274102174115824234185492081/15625000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-210007980643250337402445240721817715000000000000)
      constant := (6062072848309689112762497150824929258609736371840) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree111.table
  base := (8549784836781147400056180688632844844299/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-210496850954194646629221763957520215000000000000)
      constant := (6089840335982465809195974088436913666201862313196) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 111 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 111 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262124358931206894693/50000000000000000000)
  centralHi := (524248717862413789387/100000000000000000000)
  directionLo := (526626275265682517739/100000000000000000000)
  directionHi := (26331313763284125887/5000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree112.table
  base := (554911561258279555721274951386262958727/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-211899512365271616021508134408930415000000000000)
      constant := (6173901293672764692703184394982673531534076206528) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree112.table
  base := (2219646242662324893467854213750671487159/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 91980030000000000000000000000000000000000000000
      center := (1674036546)
      previous := (837018273)
      next := (837018273)
      square := (5552509715438824580015300664097800000000000000)
      linear := (-637178360739754378696929014102431245000000000000)
      constant := (18606513877669664937647489433911702321454447095632) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 112 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 112 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (526626275265682517739/100000000000000000000)
  centralHi := (26331313763284125887/5000000000000000000)
  directionLo := (52899314685544660067/10000000000000000000)
  directionHi := (528993146855446600671/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree113.table
  base := (36850183937698009323434415780988554044739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-213791044087292894640571028096043115000000000000)
      constant := (6286759592818339275966755478100637313939723818739) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree113.table
  base := (36850183905301038914996903685949722021801/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-214288722872308272502064245444100615000000000000)
      constant := (6315536609225313037712943618929224691168563887801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 113 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 113 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52899314685544660067/10000000000000000000)
  centralHi := (528993146855446600671/100000000000000000000)
  directionLo := (531349475430106897163/100000000000000000000)
  directionHi := (132837368857526724291/25000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree114.table
  base := (38206671440517768814407911932323538116543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-215682575809314173259633921783155815000000000000)
      constant := (6400647745738680377834642786202285647688858954543) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree114.table
  base := (38206671412850793670342849473383287695331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-216184658831365085438485486187390815000000000000)
      constant := (6429936285981426597962715548243196568457172541331) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 114 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 114 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (531349475430106897163/100000000000000000000)
  centralHi := (132837368857526724291/25000000000000000000)
  directionLo := (13342385015891823599/2500000000000000000)
  directionHi := (533695400635672943961/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree115.table
  base := (39583802426971977926677346428955838234019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-217574107531335451878696815470268515000000000000)
      constant := (6515565752427603285273021277373260972731340488019) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree115.table
  base := (9895950600836550491901898978484704829353/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 91980030000000000000000000000000000000000000000
      center := (1674036546)
      previous := (837018273)
      next := (837018273)
      square := (5552509715438824580015300664097800000000000000)
      linear := (-654241784371265695124720180792043045000000000000)
      constant := (19636110968457208377251816486218431239398013528236) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 115 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 115 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13342385015891823599/2500000000000000000)
  centralHi := (533695400635672943961/100000000000000000000)
  directionLo := (268015529531169672857/50000000000000000000)
  directionHi := (107206211812467869143/20000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree116.table
  base := (20490788447733647538467382010353346927241/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-219465639253356730497759709157381215000000000000)
      constant := (6631513612880222811394127177508559959064535666482) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree116.table
  base := (40981576875293939208553682232868675435707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-219976530749478711311327967673971215000000000000)
      constant := (6661838719733663086365092807445229181754553097707) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 116 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 116 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268015529531169672857/50000000000000000000)
  centralHi := (107206211812467869143/20000000000000000000)
  directionLo := (134589146084322771861/25000000000000000000)
  directionHi := (107671316867458217489/20000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree117.table
  base := (42399994844765814656878763824945148023821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-221357170975378009116822602844493915000000000000)
      constant := (6748491327092743536365002783200635210036183209821) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree117.table
  base := (42399994827541640068885758133008877153183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-221872466708535524247749208417261415000000000000)
      constant := (6779341476721674326569522616053997817860536231183) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 117 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 117 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (134589146084322771861/25000000000000000000)
  centralHi := (107671316867458217489/20000000000000000000)
  directionLo := (6758401340173952461/1250000000000000000)
  directionHi := (540672107213916196881/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree118.table
  base := (43839056273927273604298225932037190865397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-223248702697399287735885496531606615000000000000)
      constant := (6866498895062282612696645738595428941730498067397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree118.table
  base := (10959764064805548246830808965032101507083/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 91980030000000000000000000000000000000000000000
      center := (1674036546)
      previous := (837018273)
      next := (837018273)
      square := (5552509715438824580015300664097800000000000000)
      linear := (-671305208002777011552511347481654845000000000000)
      constant := (20693635781341333844349691233692168794033815820996) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 118 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 118 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6758401340173952461/1250000000000000000)
  centralHi := (540672107213916196881/100000000000000000000)
  directionLo := (135744438914398573013/25000000000000000000)
  directionHi := (542977755657594292053/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree119.table
  base := (2831172573891265262982600222519198026879/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1930838)
      previous := (965419)
      next := (965419)
      square := (6404278795200489711667013453400000000000000)
      linear := (-779031953008375662127849101102835000000000000)
      constant := (24171405940438477931952444878161857499874548976) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree119.table
  base := (45298761169706720964976904278497370426143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1930838)
      previous := (965419)
      next := (965419)
      square := (6404278795200489711667013453400000000000000)
      linear := (-780845462375948616334227300705335000000000000)
      constant := (24281834155391161984424722743058981102850951087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 119 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 119 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (135744438914398573013/25000000000000000000)
  centralHi := (542977755657594292053/100000000000000000000)
  directionLo := (272636827464110142381/50000000000000000000)
  directionHi := (545273654928220284763/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree120.table
  base := (374232876554247434831630348286370081619/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-227031766141441844974011283905832015000000000000)
      constant := (7105603592264572742844981977254217919576741952375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree120.table
  base := (23389554779282453885714918716366526370349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-227560274585705963057012930647132015000000000000)
      constant := (7138055908103158572723291475197836272436032808698) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 120 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 120 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (272636827464110142381/50000000000000000000)
  centralHi := (545273654928220284763/100000000000000000000)
  directionLo := (273779963829806914273/50000000000000000000)
  directionHi := (547559927659613828547/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree121.table
  base := (386240811477427111868393978601275662797/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-228923297863463123593074177592944715000000000000)
      constant := (7226700721494887131695621849742967919176408099625) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree121.table
  base := (12070025356382883777235363731214866997263/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 91980030000000000000000000000000000000000000000
      center := (1674036546)
      previous := (837018273)
      next := (837018273)
      square := (5552509715438824580015300664097800000000000000)
      linear := (-688368631634288327980302514171266645000000000000)
      constant := (21779088316094909198672337904053961093641704263156) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 121 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 121 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273779963829806914273/50000000000000000000)
  centralHi := (547559927659613828547/100000000000000000000)
  directionLo := (274918346967978479649/50000000000000000000)
  directionHi := (549836693935956959299/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree122.table
  base := (3112608548642825402918657245334983244087/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-230814829585484402212137071280057415000000000000)
      constant := (7348827704477149989270443766802266280881663777392) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree122.table
  base := (24900868385239135487773281856835975375113/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-231352146503819588929855412133712415000000000000)
      constant := (7382370662693085827954851067374971269672143666226) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 122 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 122 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (274918346967978479649/50000000000000000000)
  centralHi := (549836693935956959299/100000000000000000000)
  directionLo := (552104071365394739801/100000000000000000000)
  directionHi := (276052035682697369901/50000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree123.table
  base := (25672007800026377879762887398106198127357/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-232706361307505680831199964967170115000000000000)
      constant := (7471984541211212228254258466516082216879349378714) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree123.table
  base := (51344015593389897278773729208334147051793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-233248082462876401866276652877002615000000000000)
      constant := (7506079580087460199228771262341850135694944389793) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 123 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 123 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (552104071365394739801/100000000000000000000)
  centralHi := (276052035682697369901/50000000000000000000)
  directionLo := (554362175150926551087/100000000000000000000)
  directionHi := (34647635946932909443/6250000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree124.table
  base := (13226734475007589921960463941452870986657/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-234597893029526959450262858654282815000000000000)
      constant := (7596171231697225072296364725080183860591845394628) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree124.table
  base := (52906937894344289819437117019537266799221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 91980030000000000000000000000000000000000000000
      center := (1674036546)
      previous := (837018273)
      next := (837018273)
      square := (5552509715438824580015300664097800000000000000)
      linear := (-705432055265799644408093680860878445000000000000)
      constant := (22892468572644994841987135756485505468631035155663) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 124 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 124 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (554362175150926551087/100000000000000000000)
  centralHi := (34647635946932909443/6250000000000000000)
  directionLo := (139152779539677235359/25000000000000000000)
  directionHi := (556611118158708941437/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree125.table
  base := (6811312959793467215069996009540416520753/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-236489424751548238069325752341395515000000000000)
      constant := (7721387775935586241479489930944262443994361750024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree125.table
  base := (27245251836747784794168418918735862279379/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-237039954380990027739119134363583015000000000000)
      constant := (7756600495076172607367587167011160832468876586758) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 125 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 125 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139152779539677235359/25000000000000000000)
  centralHi := (556611118158708941437/100000000000000000000)
  directionLo := (139712752745971154531/25000000000000000000)
  directionHi := (894161617574215389/160000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree126.table
  base := (28047356467600117687979715956323685804581/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-238380956473569516688388646028508215000000000000)
      constant := (7847634173926894665358023998074539806501062301162) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree126.table
  base := (56094712931059933858252229764894641428081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-238935890340046840675540375106873215000000000000)
      constant := (7883412492671646040398935730292218600513137774081) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 126 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 126 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139712752745971154531/25000000000000000000)
  centralHi := (894161617574215389/160000000000000000)
  directionLo := (140270490503511555033/25000000000000000000)
  directionHi := (561081962014046220133/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree127.table
  base := (28859782835418202241092179758476686612439/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-240272488195590795307451539715620915000000000000)
      constant := (7974910425671912404085608602749620708010849172878) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree127.table
  base := (57719565667303751314354166235594586420233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 91980030000000000000000000000000000000000000000
      center := (1674036546)
      previous := (837018273)
      next := (837018273)
      square := (5552509715438824580015300664097800000000000000)
      linear := (-722495478897310960835884847550490245000000000000)
      constant := (24033776551006705799234580575371632940177062394699) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 127 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 127 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (140270490503511555033/25000000000000000000)
  centralHi := (561081962014046220133/100000000000000000000)
  directionLo := (28165203874521895821/5000000000000000000)
  directionHi := (563304077490437916421/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree128.table
  base := (3710316367846723141594030281864938070903/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-242164019917612073926514433402733615000000000000)
      constant := (8103216531171532661097311974519991231845226702448) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree128.table
  base := (59365061882533569567728231560281168044787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-242727762258160466548382856593453615000000000000)
      constant := (8140139568068880160687496564088357941506484986787) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 128 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 128 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28165203874521895821/5000000000000000000)
  centralHi := (563304077490437916421/100000000000000000000)
  directionLo := (113103492313398522101/20000000000000000000)
  directionHi := (282758730783496305253/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree129.table
  base := (15257800394914769277141652227124973064789/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-244055551639633352545577327089846315000000000000)
      constant := (8232552490426752942595673591017175144416464555156) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree129.table
  base := (30515600788543868816319255708477869034687/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-244623698217217279484804097336743815000000000000)
      constant := (8270054645872618101642927548138497307376438753374) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 129 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 129 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113103492313398522101/20000000000000000000)
  centralHi := (282758730783496305253/50000000000000000000)
  directionLo := (17741319261478049251/3125000000000000000)
  directionHi := (567722216367297576033/100000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree130.table
  base := (3135899237676147613297417343425205893063/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-245947083361654631164640220776959015000000000000)
      constant := (8362918303438652564495255671819758381366741021260) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree130.table
  base := (15679496187832347959028295452626801213029/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 91980030000000000000000000000000000000000000000
      center := (1674036546)
      previous := (837018273)
      next := (837018273)
      square := (5552509715438824580015300664097800000000000000)
      linear := (-739558902528822277263676014240102045000000000000)
      constant := (25203012251243687396858873575800383426751377524348) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 130 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 130 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17741319261478049251/3125000000000000000)
  centralHi := (567722216367297576033/100000000000000000000)
  directionLo := (569918442039576679583/100000000000000000000)
  directionHi := (17809951313736771237/3125000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree131.table
  base := (12885082281502353393244792619020059746039/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-247838615083675909783703114464071715000000000000)
      constant := (8494313970208373830555438141088297894757076600195) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree131.table
  base := (4026588212852537028286586229164982997047/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-248415570135330905357646578823324215000000000000)
      constant := (8532987881695884649801059767720595325042865584752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 131 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 131 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (569918442039576679583/100000000000000000000)
  centralHi := (17809951313736771237/3125000000000000000)
  directionLo := (143026559202443236847/25000000000000000000)
  directionHi := (572106236809772947389/100000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree132.table
  base := (66153481542013508306256904587320374394509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-249730146805697188402766008151184415000000000000)
      constant := (8626739490737106309603191424185272610213938988509) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree132.table
  base := (6615348154041743120332783655606647684879/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-250311506094387718294067819566614415000000000000)
      constant := (8666006039717799071800747191768438004084866988790) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 132 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 132 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143026559202443236847/25000000000000000000)
  centralHi := (572106236809772947389/100000000000000000000)
  directionLo := (143571424258202771101/25000000000000000000)
  directionHi := (114857139406562216881/20000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree133.table
  base := (13580439031485460820159881062167918972437/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-251621678527718467021828901838297115000000000000)
      constant := (8760194865026073727917673685201676809937054072185) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree133.table
  base := (13580439031213191509956761096868019818143/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 91980030000000000000000000000000000000000000000
      center := (1674036546)
      previous := (837018273)
      next := (837018273)
      square := (5552509715438824580015300664097800000000000000)
      linear := (-756622326160333593691467180929713845000000000000)
      constant := (26400175673444652039020563817705799806956693842145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 133 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 133 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143571424258202771101/25000000000000000000)
  centralHi := (114857139406562216881/20000000000000000000)
  directionLo := (288228458621057820659/50000000000000000000)
  directionHi := (576456917242115641319/100000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree134.table
  base := (6967155225415986718975114312876364343731/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-253513210249739745640891795525409815000000000000)
      constant := (8894680093076523067472730176365470382042435897310) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree134.table
  base := (34835776126499397609846971284976403675419/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-254103378012501344166910301053194815000000000000)
      constant := (8935145435988404578181258589521034362290476658838) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 134 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 134 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (288228458621057820659/50000000000000000000)
  centralHi := (576456917242115641319/100000000000000000000)
  directionLo := (578619990197456832361/100000000000000000000)
  directionHi := (289309995098728416181/50000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree135.table
  base := (3573077641631127315236396034402822331349/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-255404741971761024259954689212522515000000000000)
      constant := (9030195174889715523890843680208047372164767306980) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree135.table
  base := (446634705197702126834671247952125023597/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-255999313971558157103331541796485015000000000000)
      constant := (9071266674239637438123134962715922086415748095520) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 135 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 135 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (578619990197456832361/100000000000000000000)
  centralHi := (289309995098728416181/50000000000000000000)
  directionLo := (290387503465596260229/50000000000000000000)
  directionHi := (580775006931192520459/100000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree136.table
  base := (18318049223307222007495124820959705257749/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1930838)
      previous := (965419)
      next := (965419)
      square := (6404278795200489711667013453400000000000000)
      linear := (-890298524891980286778607553285935000000000000)
      constant := (31718823911650238863020323927719756052317836564) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree136.table
  base := (18318049223096112250869175161658250540941/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 318270000000000000000000000000000000000000000
      center := (5792514)
      previous := (2896257)
      next := (2896257)
      square := (19212836385601469135001040360200000000000000)
      linear := (-2677113321079048131900547915637805000000000000)
      constant := (95589158538787512876727248537290168559866116828) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 136 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 136 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (290387503465596260229/50000000000000000000)
  centralHi := (580775006931192520459/100000000000000000000)
  directionLo := (291461028396485796619/50000000000000000000)
  directionHi := (582922056792971593239/100000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree137.table
  base := (75103484436392629146156036326945899818921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-259187805415803581498080476586747915000000000000)
      constant := (9304314899809402107422020946343134692040711604921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree137.table
  base := (75103484435672537628710732618266981583539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-259791185889671782976174023283065415000000000000)
      constant := (9346612230980363283915560575805598201302112157539) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 137 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 137 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291461028396485796619/50000000000000000000)
  centralHi := (582922056792971593239/100000000000000000000)
  directionLo := (585061227492960841647/100000000000000000000)
  directionHi := (36566326718310052603/6250000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree138.table
  base := (76955415462526051130310986892076994367599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-261079337137824860117143370273860615000000000000)
      constant := (9442919542918428807339222242219906114308052901599) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree138.table
  base := (76955415461912028910028538991733542229511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-261687121848728595912595264026355615000000000000)
      constant := (9485836549472409755034293150713072627209222955511) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 138 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 138 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (585061227492960841647/100000000000000000000)
  centralHi := (36566326718310052603/6250000000000000000)
  directionLo := (58719260514365451127/10000000000000000000)
  directionHi := (587192605143654511271/100000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree139.table
  base := (78827989972038639150236556227264779500347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-262970868859846138736206263960973315000000000000)
      constant := (9582554039795254613098410505822997194962843402347) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree139.table
  base := (315311959886060358351561871662795504293/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 91980030000000000000000000000000000000000000000
      center := (1674036546)
      previous := (837018273)
      next := (837018273)
      square := (5552509715438824580015300664097800000000000000)
      linear := (-790749173423356226547049514308937445000000000000)
      constant := (28878285684141800572358022505096604626718381719750) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 139 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 139 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58719260514365451127/10000000000000000000)
  centralHi := (587192605143654511271/100000000000000000000)
  directionLo := (589316274300322914317/100000000000000000000)
  directionHi := (294658137150161457159/50000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree140.table
  base := (80721207965335996830375442432769421839471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-264862400581867417355269157648086015000000000000)
      constant := (9723218390441123105817730673970503705129239925471) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree140.table
  base := (80721207964889612280713448956462931093393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-265478993766842221785437745512936015000000000000)
      constant := (9767388266706185190346662553230190153195274031393) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 140 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 140 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (589316274300322914317/100000000000000000000)
  centralHi := (294658137150161457159/50000000000000000000)
  directionLo := (591432318000153858031/100000000000000000000)
  directionHi := (36964519875009616127/6250000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree141.table
  base := (82635069442818975629978797481930767054927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-266753932303888695974332051335198715000000000000)
      constant := (9864912594857263296472098237863837584971173236927) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree141.table
  base := (161396620004762504302379342884401508607/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-267374929725899034721858986256226215000000000000)
      constant := (9909715665450399754906170912891367497312772150784) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 141 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 141 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (591432318000153858031/100000000000000000000)
  centralHi := (36964519875009616127/6250000000000000000)
  directionLo := (593540817800138153761/100000000000000000000)
  directionHi := (296770408900069076881/50000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree142.table
  base := (42284787202441492036481088186037388522607/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-268645464025909974593394945022311415000000000000)
      constant := (10007636653044887507991246813040355230995403169214) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree142.table
  base := (3382782976182341415217764448551074611813/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 91980030000000000000000000000000000000000000000
      center := (1674036546)
      previous := (837018273)
      next := (837018273)
      square := (5552509715438824580015300664097800000000000000)
      linear := (-807812597054867542974840680998549245000000000000)
      constant := (30159232272843383959874175081498804963316995235975) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 142 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 142 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (593540817800138153761/100000000000000000000)
  centralHi := (296770408900069076881/50000000000000000000)
  directionLo := (595641853813748111803/100000000000000000000)
  directionHi := (148910463453437027951/25000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree143.table
  base := (86524722851917447482031650874620140468059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-270536995747931253212457838709424115000000000000)
      constant := (10151390565005189718804018538257298114045209362059) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree143.table
  base := (43262361425820430115987798940867759801349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-271166801644012660594701467742806615000000000000)
      constant := (10197473543199568227143940148375515967337391670698) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 143 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 143 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (595641853813748111803/100000000000000000000)
  centralHi := (148910463453437027951/25000000000000000000)
  directionLo := (597735504746455692293/100000000000000000000)
  directionHi := (298867752373227846147/50000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree144.table
  base := (44250257392152696724240237230885309947821/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-272428527469952531831520732396536815000000000000)
      constant := (10296174330739344291888346119953696442370658267642) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree144.table
  base := (44250257392034809390803184175675563762167/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-273062737603069473531122708486096815000000000000)
      constant := (10342904022206898562894236138280963668340735568334) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 144 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 144 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (597735504746455692293/100000000000000000000)
  centralHi := (298867752373227846147/50000000000000000000)
  directionLo := (599821847930134864689/100000000000000000000)
  directionHi := (59982184793013486469/10000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree145.table
  base := (45248475101211571070889568302323805049867/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-274320059191973810450583626083649515000000000000)
      constant := (10441987950248505025260146248318497883463394543734) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree145.table
  base := (18099390040444433499600623570870487030571/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 91980030000000000000000000000000000000000000000
      center := (1674036546)
      previous := (837018273)
      next := (837018273)
      square := (5552509715438824580015300664097800000000000000)
      linear := (-824876020686378859402631847688161045000000000000)
      constant := (31468106583912827907557704659389360974093265748565) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 145 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 145 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (599821847930134864689/100000000000000000000)
  centralHi := (59982184793013486469/10000000000000000000)
  directionLo := (9404702489943605011/1562500000000000000)
  directionHi := (120380191871278144141/20000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree146.table
  base := (18502805821328016767640365512297246536909/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-276211590913995089069646519770762215000000000000)
      constant := (10588831423533804469875865866957641578397047654545) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree146.table
  base := (92514029106468780895982522300786592846367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-276854609521183099403965189972677215000000000000)
      constant := (10636868060492835708051638836078866409453554068367) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 146 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 146 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9404702489943605011/1562500000000000000)
  centralHi := (120380191871278144141/20000000000000000000)
  directionLo := (603972913708855981571/100000000000000000000)
  directionHi := (150993228427213995393/25000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree147.table
  base := (47275875748659264408550300595618672028849/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-278103122636016367688709413457874915000000000000)
      constant := (10736704750596353469414308652354724711868246125698) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree147.table
  base := (94551751497172523698506596832391853861381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-278750545480239912340386430715967415000000000000)
      constant := (10785401619773690936295114248514786548830848007381) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 147 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 147 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (603972913708855981571/100000000000000000000)
  centralHi := (150993228427213995393/25000000000000000000)
  directionLo := (30301889219724686709/5000000000000000000)
  directionHi := (606037784394493734181/100000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree148.table
  base := (24152529343703404278701665743073100018429/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-279994654358037646307772307144987615000000000000)
      constant := (10885607931437240883582006116837700965918413329716) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree148.table
  base := (24152529343672294900877409182081165109519/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 91980030000000000000000000000000000000000000000
      center := (1674036546)
      previous := (837018273)
      next := (837018273)
      square := (5552509715438824580015300664097800000000000000)
      linear := (-841939444317890175830423014377772845000000000000)
      constant := (32804908617443797461269934113093209021683404362228) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 148 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 148 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30301889219724686709/5000000000000000000)
  centralHi := (606037784394493734181/100000000000000000000)
  directionLo := (608095643573943516287/100000000000000000000)
  directionHi := (4750747215421433721/781250000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree149.table
  base := (98689126739473277605322389502608580632511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-281886186080058924926835200832100315000000000000)
      constant := (11035540966057533462654578421058283652077859358511) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree149.table
  base := (98689126739367226598717337287482697391147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-282542417398353538213228912202547815000000000000)
      constant := (11085571818616628794295075173139831385183954093147) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 149 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 149 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (608095643573943516287/100000000000000000000)
  centralHi := (4750747215421433721/781250000000000000)
  directionLo := (610146562190946243393/100000000000000000000)
  directionHi := (305073281095473121697/50000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree150.table
  base := (12598597448954778443709983218050116728353/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-283777717802080203545898094519213015000000000000)
      constant := (11186503854458275846095067198542709070013976210824) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree150.table
  base := (50394389795773925185726783593717919872969/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-284438353357410351149650152945838015000000000000)
      constant := (11237208458180825933568926323530369597096885653938) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 150 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 150 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (610146562190946243393/100000000000000000000)
  centralHi := (305073281095473121697/50000000000000000000)
  directionLo := (76523826250110240513/12500000000000000000)
  directionHi := (122438122000176384821/20000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree151.table
  base := (25727268982910501292310002067756772693459/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-285669249524101482164960988206325715000000000000)
      constant := (11338496596640490662423703240865808290089671949836) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree151.table
  base := (102909075931564988714928757207682453054467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 91980030000000000000000000000000000000000000000
      center := (1674036546)
      previous := (837018273)
      next := (837018273)
      square := (5552509715438824580015300664097800000000000000)
      linear := (-859002867949401492258214181067384645000000000000)
      constant := (34169638373524643275558357388549171233742346629401) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 151 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 151 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76523826250110240513/12500000000000000000)
  centralHi := (122438122000176384821/20000000000000000000)
  directionLo := (153556963899613160527/25000000000000000000)
  directionHi := (614227855598452642109/100000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree152.table
  base := (52525007879905514496103733537916497089741/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-287560781246122760784023881893438415000000000000)
      constant := (11491519192605178711174380533111829965987285991482) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree152.table
  base := (26262503939936350244035600463882489210629/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-288230225275523977022492634432418415000000000000)
      constant := (11543584817599796113631313388256792883209110898516) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 152 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 152 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (153556963899613160527/25000000000000000000)
  centralHi := (614227855598452642109/100000000000000000000)
  directionLo := (4814518487847983493/781250000000000000)
  directionHi := (123251673288908377421/20000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree153.table
  base := (209397654446220075646536947385708771201/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1930838)
      previous := (965419)
      next := (965419)
      square := (6404278795200489711667013453400000000000000)
      linear := (-1001565096775584911429366005469035000000000000)
      constant := (40296095648281381352473474605456808239079761408) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree153.table
  base := (26802899769102189388966001533822391889401/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1930838)
      previous := (965419)
      next := (965419)
      square := (6404278795200489711667013453400000000000000)
      linear := (-1003896751676750138266137976386535000000000000)
      constant := (40478631617496716639006708660430104522218620836) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 153 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 153 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4814518487847983493/781250000000000000)
  centralHi := (123251673288908377421/20000000000000000000)
  directionLo := (618282208892279989999/100000000000000000000)
  directionHi := (61828220889227999/10000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree154.table
  base := (109393825881915393299703143569263295652849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-291343844690165318022149669267663815000000000000)
      constant := (11800653945885870099517841710322540931234930686849) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree154.table
  base := (5469691294093387264286163813863601452607/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 91980030000000000000000000000000000000000000000
      center := (1674036546)
      previous := (837018273)
      next := (837018273)
      square := (5552509715438824580015300664097800000000000000)
      linear := (-876066291580912808686005347756996445000000000000)
      constant := (35562295852238314325348376652812254060037670876420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 154 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 154 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (618282208892279989999/100000000000000000000)
  centralHi := (61828220889227999/10000000000000000)
  directionLo := (620299448212344155513/100000000000000000000)
  directionHi := (310149724106172077757/50000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree155.table
  base := (2231933923529375645973086400198216836689/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-293235376412186596641212562954776515000000000000)
      constant := (11956766103203768376473894901243891944725265534450) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree155.table
  base := (27899174044107046298635389778902852837653/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-293918033152694415831756356662289015000000000000)
      constant := (12010907057469394760541060910690948215312387742612) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 155 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 155 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (620299448212344155513/100000000000000000000)
  centralHi := (310149724106172077757/50000000000000000000)
  directionLo := (311155074308760192343/50000000000000000000)
  directionHi := (622310148617520384687/100000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree156.table
  base := (56910104980211873950474936024409574754533/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-295126908134207875260275456641889215000000000000)
      constant := (12113908114307930476094526765900593126213945865066) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree156.table
  base := (14227526245048644969422974176571150407601/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-295813969111751228768177597405579215000000000000)
      constant := (12168749857627338052109244457434923279766840588808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 156 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 156 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311155074308760192343/50000000000000000000)
  centralHi := (622310148617520384687/100000000000000000000)
  directionLo := (312157186643276718491/50000000000000000000)
  directionHi := (624314373286553436983/100000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree157.table
  base := (116064367234072614585038275773387901553441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-297018439856229153879338350329001915000000000000)
      constant := (12272079979199252665522984810425087990800751659441) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree157.table
  base := (23212873446808629438615710715140366351573/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 91980030000000000000000000000000000000000000000
      center := (1674036546)
      previous := (837018273)
      next := (837018273)
      square := (5552509715438824580015300664097800000000000000)
      linear := (-893129715212424125113796514446608245000000000000)
      constant := (36982881053662494165051436475394456878114337543595) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 157 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 157 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312157186643276718491/50000000000000000000)
  centralHi := (624314373286553436983/100000000000000000000)
  directionLo := (125262436877461978773/20000000000000000000)
  directionHi := (313156092193654946933/50000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree158.table
  base := (118329167997701264590007537886697354509623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-298909971578250432498401244016114615000000000000)
      constant := (12431281697878611459990195102457027308123858627623) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree158.table
  base := (7395572999854760052703012878620659415897/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-299605841029864854641020078892159615000000000000)
      constant := (12487538538250751686437795524947658271236793886352) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 158 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 158 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (125262436877461978773/20000000000000000000)
  centralHi := (313156092193654946933/50000000000000000000)
  directionLo := (628303643099278349697/100000000000000000000)
  directionHi := (314151821549639174849/50000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree159.table
  base := (4824584490063571093298322307440857545793/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-300801503300271711117464137703227315000000000000)
      constant := (12591513270346864050267033882842252245656472094825) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree159.table
  base := (4824584490062715676005729185782980544963/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-301501776988921667577441319635449815000000000000)
      constant := (12648484418717956479852457719089708525845927574075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 159 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 159 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (628303643099278349697/100000000000000000000)
  centralHi := (314151821549639174849/50000000000000000000)
  directionLo := (630288809635429768979/100000000000000000000)
  directionHi := (31514440481771488449/5000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree160.table
  base := (61460349998005035664855084185955688724033/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-302693035022292989736527031390340015000000000000)
      constant := (12752774696604848737801023810493986055167147804066) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree160.table
  base := (122920699995991854181875859636838029908563/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 91980030000000000000000000000000000000000000000
      center := (1674036546)
      previous := (837018273)
      next := (837018273)
      square := (5552509715438824580015300664097800000000000000)
      linear := (-910193138843935441541587681136220045000000000000)
      constant := (38431393977869853086702934017310092309613052199689) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 160 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 160 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (630288809635429768979/100000000000000000000)
  centralHi := (31514440481771488449/5000000000000000000)
  directionLo := (79033467907932513561/12500000000000000000)
  directionHi := (632267743263460108489/100000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree161.table
  base := (125247431231231047431206921710468939524257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-304584566744314268355589925077452715000000000000)
      constant := (12915065976653385373863958131570148525300311486257) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree161.table
  base := (6262371561560776489326688197947393864389/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-305293648907035293450283801122030215000000000000)
      constant := (12973479259967555433963575272931972228212210767780) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 161 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 161 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79033467907932513561/12500000000000000000)
  centralHi := (632267743263460108489/100000000000000000000)
  directionLo := (634240502326436406533/100000000000000000000)
  directionHi := (317120251163218203267/50000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree162.table
  base := (63797402978756866188064048564179895796289/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-306476098466335546974652818764565415000000000000)
      constant := (13078387110493275799699688788972676016882635740578) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree162.table
  base := (127594805957500514718342578583836619082387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-307189584866092106386705041865320415000000000000)
      constant := (13137528220751571748650801324694180112943217624387) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 162 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 162 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (634240502326436406533/100000000000000000000)
  centralHi := (317120251163218203267/50000000000000000000)
  directionLo := (318103572131433343409/50000000000000000000)
  directionHi := (636207144262866686819/100000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree163.table
  base := (32490706043778480469191934169565103688671/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-308367630188356825593715712451678115000000000000)
      constant := (13242738098125304285217905027929116673648275898684) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree163.table
  base := (32490706043775665933910284570030797338919/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 91980030000000000000000000000000000000000000000
      center := (1674036546)
      previous := (837018273)
      next := (837018273)
      square := (5552509715438824580015300664097800000000000000)
      linear := (-927256562475446757969378847825831845000000000000)
      constant := (39907834624928353271722733360388224533563075915028) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 163 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 163 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (318103572131433343409/50000000000000000000)
  centralHi := (636207144262866686819/100000000000000000000)
  directionLo := (638167725626213209257/100000000000000000000)
  directionHi := (319083862813106604629/50000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree164.table
  base := (26470297176856364515905576262473996106453/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-310259161910378104212778606138790815000000000000)
      constant := (13408118939550237964246682152400954107681905022265) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree164.table
  base := (3308787147106805845427410804941338476099/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-310981456784205732259547523351900815000000000000)
      constant := (13468729222641960747880754626638073258362320403960) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 164 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 164 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (638167725626213209257/100000000000000000000)
  centralHi := (319083862813106604629/50000000000000000000)
  directionLo := (128024460420773564459/20000000000000000000)
  directionHi := (80015287762983477787/12500000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree165.table
  base := (8422549442828887023937464915831038249099/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-312150693632399382831841499825903515000000000000)
      constant := (13574529634768827264747857783750012446894412529584) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree165.table
  base := (67380395542627012881840410092849439508071/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-312877392743262545195968764095191015000000000000)
      constant := (13635881263749851280070913900490400736262370388142) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 165 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 165 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128024460420773564459/20000000000000000000)
  centralHi := (80015287762983477787/12500000000000000000)
  directionLo := (642070928535607429149/100000000000000000000)
  directionHi := (12841418570712148583/2000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree166.table
  base := (137190739778294478699388606775276793748971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-314042225354420661450904393513016215000000000000)
      constant := (13741970183781806332726703537478098827411138834971) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree166.table
  base := (6859536988914376177757551774447467570853/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 91980030000000000000000000000000000000000000000
      center := (1674036546)
      previous := (837018273)
      next := (837018273)
      square := (5552509715438824580015300664097800000000000000)
      linear := (-944319986106958074397170014515443645000000000000)
      constant := (41412202994901570835798421196714031496182172131180) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 166 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 166 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (642070928535607429149/100000000000000000000)
  centralHi := (12841418570712148583/2000000000000000000)
  directionLo := (644013658931546871777/100000000000000000000)
  directionHi := (322006829465773435889/50000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree167.table
  base := (139641331963612954334761431139174383049607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-315933757076441940069967287200128915000000000000)
      constant := (13910440586589893448840890715034267296354478111607) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree167.table
  base := (27928266392721406232845147501604442309891/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-316669264661376171068811245581771415000000000000)
      constant := (13973288426294696119681093504321854451132840579455) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 167 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 167 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (644013658931546871777/100000000000000000000)
  centralHi := (322006829465773435889/50000000000000000000)
  directionLo := (645950546489605859873/100000000000000000000)
  directionHi := (322975273244802929937/50000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree168.table
  base := (71056283820723425368986981250588280762087/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-317825288798463218689030180887241615000000000000)
      constant := (14079940843193791436941843416893038508809679008174) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree168.table
  base := (142112567641441806601991421269893890990471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-318565200620432984005232486325061615000000000000)
      constant := (14143543547733071708607022421581137359670675076471) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 168 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 168 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell084.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (645950546489605859873/100000000000000000000)
  centralHi := (322975273244802929937/50000000000000000000)
  directionLo := (323940821806252962971/50000000000000000000)
  directionHi := (647881643612505925943/100000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 3579
  qDenominator := 7004
  table := BinomialMassData.Q3579_7004.Degree169.table
  base := (144604446812020488430060039852361899150943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30660010000000000000000000000000000000000000000
      center := (558012182)
      previous := (279006091)
      next := (279006091)
      square := (1850836571812941526671766888032600000000000000)
      linear := (-319716820520484497308093074574354315000000000000)
      constant := (14250470953594188063971371914434898351408690388943) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q3579_7004.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 5381
  qDenominator := 10506
  table := BinomialMassData.Q5381_10506.Degree169.table
  base := (4518888962875506032078217497792251719461/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 91980030000000000000000000000000000000000000000
      center := (1674036546)
      previous := (837018273)
      next := (837018273)
      square := (5552509715438824580015300664097800000000000000)
      linear := (-961383409738469390824961181205055445000000000000)
      constant := (42944499087849014645172599649489934082655437964256) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q5381_10506.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 169 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 169 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell084.Kernel169
