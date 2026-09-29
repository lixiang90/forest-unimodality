import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell202.Parameters
import ForestUnimodality.BinomialMassData.Q12116_22791.Batch000_049
import ForestUnimodality.BinomialMassData.Q12116_22791.Batch050_099
import ForestUnimodality.BinomialMassData.Q12116_22791.Batch100_149
import ForestUnimodality.BinomialMassData.Q12116_22791.Batch150_199
import ForestUnimodality.BinomialMassData.Q24257_45582.Batch000_049
import ForestUnimodality.BinomialMassData.Q24257_45582.Batch050_099
import ForestUnimodality.BinomialMassData.Q24257_45582.Batch100_149
import ForestUnimodality.BinomialMassData.Q24257_45582.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree000.table
  base := (43971456815013081976246667/500000000000000000000000)
  polynomial :=
    { denominator := 1250000000000000000000000000000000000000
      center := (22)
      previous := (11)
      next := (11)
      square := (77085905819958989299012231250000000000)
      linear := (-5715443353417988189835163875000000000)
      constant := (109928642037532704940616667500000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree000.table
  base := (43971456815013081976246667/500000000000000000000000)
  polynomial :=
    { denominator := 1250000000000000000000000000000000000000
      center := (22)
      previous := (11)
      next := (11)
      square := (77085905819958989299012231250000000000)
      linear := (-5715443353417988189835163875000000000)
      constant := (109928642037532704940616667500000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree001.table
  base := (489879435046951141908122720840351323709541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-364328965431342613306121213384840991000000000000)
      constant := (254561072700010826263971719581774865718374618286421) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree001.table
  base := (489478600608943974509642781533771972211143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-364680338407251150371143970937324741000000000000)
      constant := (254353067312734261000974174266385033543374873135383) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (623705681599537789/1250000000000000000)
  directionHi := (49896454527963023121/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree002.table
  base := (144299457160305924042748756444886152882417/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160162829878629364978673347573142925000000000000)
      linear := (-352453881759984709845689826928145095500000000000)
      constant := (75147103145306251177212430061016103789031092818977) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree002.table
  base := (2251452133622529530529241749570780944887/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40040707469657341244668336893285731250000000000)
      linear := (-88201313683973311727678146120157211375000000000)
      constant := (18760054254861882306133467993280994868351527856752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (623705681599537789/1250000000000000000)
  centralHi := (49896454527963023121/100000000000000000000)
  directionLo := (17641060676944433917/25000000000000000000)
  directionHi := (70564242707777735669/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree003.table
  base := (11368241433614742004466321772575104732517/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4448967496628593471629815210365081250000000000)
      linear := (-14520646689008280917731084643440824875000000000)
      constant := (1324064765712357794388190863373728527000643474906) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree003.table
  base := (22695618409368614927875085697051720623081/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4448967496628593471629815210365081250000000000)
      linear := (-14535287229671136628773699541460981125000000000)
      constant := (1321730201796147430050735043184668707194231674129) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17641060676944433917/25000000000000000000)
  centralHi := (70564242707777735669/100000000000000000000)
  directionLo := (86423194359982118269/100000000000000000000)
  directionHi := (8642319435998211827/10000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree004.table
  base := (123140371040259292631860834970373386129347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-1386065359697223032461896534799188591000000000000)
      constant := (65461717175425875999981254502928030472056536948307) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree004.table
  base := (30725549645433796616812682021783977888729/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80081414939314682489336673786571462500000000000)
      linear := (-346867712900214295180496891252280897750000000000)
      constant := (16335261422582336024245230712936224964153557965449) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86423194359982118269/100000000000000000000)
  centralHi := (8642319435998211827/10000000000000000000)
  directionLo := (623705681599537789/625000000000000000)
  directionHi := (99792909055926046241/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree005.table
  base := (22268524913321824139451721421771028712399/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80081414939314682489336673786571462500000000000)
      linear := (-431661039446462459711788743817659447750000000000)
      constant := (12148515918171298959292810160950647044123253314719) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree005.table
  base := (88903477192321224367725123601410844626123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-1728401022665392524172268763033056541000000000000)
      constant := (48510174705658017871628666621434715879087634156763) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (623705681599537789/625000000000000000)
  centralHi := (99792909055926046241/100000000000000000000)
  directionLo := (111571864160752500899/100000000000000000000)
  directionHi := (1115718641607525009/1000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree006.table
  base := (13601731793299159797685249345093926349411/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-229691439541608516136934823971342999000000000000)
      constant := (4295609305684387537057720097338314187728916815495) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree006.table
  base := (67884145745726238574608389672766218078319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-229925688192214207513616662339665499000000000000)
      constant := (4289179346477077814162106640259262740555296798471) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111571864160752500899/100000000000000000000)
  centralHi := (1115718641607525009/1000000000000000000)
  directionLo := (30555213391873171913/25000000000000000000)
  directionHi := (122220853567492687653/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree007.table
  base := (6753475024138471135537630095326553524841/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40040707469657341244668336893285731250000000000)
      linear := (-300975219245387931452208982026692023875000000000)
      constant := (4073487773852065230247498119514321689737586205721) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree007.table
  base := (431467646009832586247248912240012323233/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-2410261364794463211072831159080922441000000000000)
      constant := (32548145725229870043693397139628689423623259834125) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30555213391873171913/25000000000000000000)
  centralHi := (122220853567492687653/100000000000000000000)
  directionLo := (132013609984832896041/100000000000000000000)
  directionHi := (66006804992416448021/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree008.table
  base := (44092887056031721029228696910913649356533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-2748380552051730258002930296684985391000000000000)
      constant := (28797961119571639777226626856486465631809791455973) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree008.table
  base := (2751138446782542412469688385205330438211/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40040707469657341244668336893285731250000000000)
      linear := (-343898941982374819315389044638106923875000000000)
      constant := (3596404942771058059507604338148252746539059881382) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132013609984832896041/100000000000000000000)
  centralHi := (66006804992416448021/50000000000000000000)
  directionLo := (17641060676944433917/12500000000000000000)
  directionHi := (141128485415555471337/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree009.table
  base := (1464357517516636192826539137106017065243/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-343217705571150784932020970795159399000000000000)
      constant := (2940242193858106452293925039219776147610354659675) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree009.table
  base := (36547442145319979860853496844083550596987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-343569078547059321997043728347643149000000000000)
      constant := (2938388044918679638511480564981803860326701885683) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17641060676944433917/12500000000000000000)
  centralHi := (141128485415555471337/100000000000000000000)
  directionLo := (1871117044798613367/1250000000000000000)
  directionHi := (149689363583889069361/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree010.table
  base := (30711478687681444263516319273760177505071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-3429538148228983870773447177627883791000000000000)
      constant := (25131524533742830254382473106330921831962405412351) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree010.table
  base := (30659260317077240448494101510451026221353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-3433051877988069241423674753152721291000000000000)
      constant := (25123220115263536596015933079247997251280024178393) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1871117044798613367/1250000000000000000)
  centralHi := (149689363583889069361/100000000000000000000)
  directionLo := (157786443475384845001/100000000000000000000)
  directionHi := (78893221737692422501/50000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree011.table
  base := (5182140576958101789189117382165210650629/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-3770116946317610677158705618099332991000000000000)
      constant := (24551575493859539229183072304596191163770119596745) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree011.table
  base := (6466359258841082201080697169656046588739/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80081414939314682489336673786571462500000000000)
      linear := (-943495512263151146218488987794163560250000000000)
      constant := (6137705039179127029410362549437153928309836962259) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157786443475384845001/100000000000000000000)
  centralHi := (78893221737692422501/50000000000000000000)
  directionLo := (82743909019141551547/50000000000000000000)
  directionHi := (33097563607656620619/20000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree012.table
  base := (2191301420429487991855553813337153559049/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17795869986514373886519260841460325000000000000)
      linear := (-228371985800346526863553558809487899500000000000)
      constant := (1364990554425692182480240939544178221013798185205) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree012.table
  base := (21873287015026293303671736743691887215537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-457212468901904436480470794355620799000000000000)
      constant := (2730695900480622305945359792570465186739373572633) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82743909019141551547/50000000000000000000)
  centralHi := (33097563607656620619/20000000000000000000)
  directionLo := (172846388719964236539/100000000000000000000)
  directionHi := (8642319435998211827/5000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree013.table
  base := (18530790611643157755468496171597015358373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-4451274542494864289929222499042231391000000000000)
      constant := (25088831537595986038879042138369850856151788069013) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree013.table
  base := (18495699322960797063443076114923467583417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-4455842391181675271774518347224520141000000000000)
      constant := (25102357985797855316074236192111882239268133199977) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172846388719964236539/100000000000000000000)
  centralHi := (8642319435998211827/5000000000000000000)
  directionLo := (179904225264428021829/100000000000000000000)
  directionHi := (17990422526442802183/10000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree014.table
  base := (15636159650866827313490189457147703638381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-4791853340583491096314480939513680591000000000000)
      constant := (26042159418647707125014118182542222094766782186461) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree014.table
  base := (15605082797171607618339663408732500302567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-4796772562246210615224799545248453091000000000000)
      constant := (26062830164559149452688305616734143895494780291127) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179904225264428021829/100000000000000000000)
  centralHi := (17990422526442802183/10000000000000000000)
  directionLo := (37339087531676584029/20000000000000000000)
  directionHi := (93347718829191460073/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree015.table
  base := (13136838339637030616201229839638119817173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-570270237630235322522193264442792199000000000000)
      constant := (3042431011416090578584859637238045719119327745757) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree015.table
  base := (13109308819498012357345685773293608941911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-570855859256749550963897860363598449000000000000)
      constant := (3045536144651921489453091739046846233559508695599) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37339087531676584029/20000000000000000000)
  centralHi := (93347718829191460073/50000000000000000000)
  directionLo := (48312034355399111757/25000000000000000000)
  directionHi := (193248137421596447029/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree016.table
  base := (10963123376111766709818242080524693536267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-5473010936760744709084997820456578991000000000000)
      constant := (29071784626046873017802503452910433332165929740827) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree016.table
  base := (170918137951659007246314666239740650057/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40040707469657341244668336893285731250000000000)
      linear := (-684829113046910162765670242662039873875000000000)
      constant := (3638397811204020665524897217388284100054721134536) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48312034355399111757/25000000000000000000)
  centralHi := (193248137421596447029/100000000000000000000)
  directionLo := (623705681599537789/312500000000000000)
  directionHi := (199585818111852092481/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree017.table
  base := (226514690364291132809745665396448267519/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40040707469657341244668336893285731250000000000)
      linear := (-726698716856171439433782032616003523875000000000)
      constant := (3885450614201889643370237850355057857151984157195) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree017.table
  base := (2259765918106548507562306748419281896169/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80081414939314682489336673786571462500000000000)
      linear := (-1454890768859954161393910784830062985250000000000)
      constant := (7781664414873070195499930004846944886326138792089) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (623705681599537789/312500000000000000)
  centralHi := (199585818111852092481/100000000000000000000)
  directionLo := (51432088090655032989/25000000000000000000)
  directionHi := (205728352362620131957/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree018.table
  base := (3692877082818655491905269667743980180393/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17795869986514373886519260841460325000000000000)
      linear := (-341898251829888795658639705633304299500000000000)
      constant := (1855264265481575372805686074690779095419095382737) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree018.table
  base := (92084690751865205245352318139288314893/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4448967496628593471629815210365081250000000000)
      linear := (-85562406201449333180915615796447012375000000000)
      constant := (464523412507559905719382197588457436121553932370) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51432088090655032989/25000000000000000000)
  centralHi := (205728352362620131957/100000000000000000000)
  directionLo := (52923182030833301751/25000000000000000000)
  directionHi := (42338545624666641401/20000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree019.table
  base := (5903369822831774531159186431576472297719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-6494747331026625128240773141870926591000000000000)
      constant := (35986928659412022078104339919946487136709517197639) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree019.table
  base := (5886668983990999067651129391587657470809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-6501423417568887332476205535368117841000000000000)
      constant := (36045968866988351438452270787516572107599585681929) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52923182030833301751/25000000000000000000)
  centralHi := (42338545624666641401/20000000000000000000)
  directionLo := (43498720585672655747/20000000000000000000)
  directionHi := (13593350183022704921/6250000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree020.table
  base := (4584573010059700024262837591385943873157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-6835326129115251934626031582342375791000000000000)
      constant := (38845128996581755681970311062197371493917844972917) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree020.table
  base := (4569906031008882276585378026364458694639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-6842353588633422675926486733392050791000000000000)
      constant := (38912527423417171063885134897509237939494012180159) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43498720585672655747/20000000000000000000)
  centralHi := (13593350183022704921/6250000000000000000)
  directionLo := (223143728321505001799/100000000000000000000)
  directionHi := (1115718641607525009/500000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree021.table
  base := (1702794476416268499803600623401946990293/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17795869986514373886519260841460325000000000000)
      linear := (-398661384844659930056182779045212499500000000000)
      constant := (2330944914813840156482479564612278941994089231837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree021.table
  base := (3392732510881687256239018494676856270737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-798142639966439779930751992379553749000000000000)
      constant := (4670335877128748133506751036698172334643529949433) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223143728321505001799/100000000000000000000)
  centralHi := (1115718641607525009/500000000000000000)
  directionLo := (114327139892156310253/50000000000000000000)
  directionHi := (228654279784312620507/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree022.table
  base := (2346755204256620314592831951741694353407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-7516483725292505547396548463285274191000000000000)
      constant := (45312353811096467556306053763578716644389699273167) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree022.table
  base := (467101148049392071301565625426187477173/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-7524213930762493362827049129439916691000000000000)
      constant := (45397252286460094544628222087923262728570830859065) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114327139892156310253/50000000000000000000)
  centralHi := (228654279784312620507/100000000000000000000)
  directionLo := (117017558338635442569/50000000000000000000)
  directionHi := (234035116677270885139/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree023.table
  base := (347941939045756714414900351934652433211/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80081414939314682489336673786571462500000000000)
      linear := (-1964265630845283088445451725939180847750000000000)
      constant := (12225674061042993342125842752370481513228663535691) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree023.table
  base := (1381940556611990456456935446390016799447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-7865144101827028706277330327463849641000000000000)
      constant := (48996756603562632990715170457179379945721396186407) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117017558338635442569/50000000000000000000)
  centralHi := (234035116677270885139/100000000000000000000)
  directionLo := (47858997905348949529/20000000000000000000)
  directionHi := (119647494763372373823/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree024.table
  base := (52708331057098167410290036187060302729/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17795869986514373886519260841460325000000000000)
      linear := (-455424517859431064453725852457120699500000000000)
      constant := (2928944498605257366308976625958592682096826610805) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree024.table
  base := (259255782591105729680623685166988223649/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17795869986514373886519260841460325000000000000)
      linear := (-455893015160642447207089529193765699500000000000)
      constant := (2934695019664600445092570788539496829637861858441) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47858997905348949529/20000000000000000000)
  centralHi := (119647494763372373823/50000000000000000000)
  directionLo := (30555213391873171913/12500000000000000000)
  directionHi := (48888341426997075061/20000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree025.table
  base := (-129281224752238952996770722125677600477/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160162829878629364978673347573142925000000000000)
      linear := (-4269110059779192983276161892349810895500000000000)
      constant := (28380708491358714485454580989936071092075386442163) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree025.table
  base := (-133014341232090453993491622116504351297/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160162829878629364978673347573142925000000000000)
      linear := (-4273502221978049696588946361755857770500000000000)
      constant := (28437335639557408930202398176099541487470687353743) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30555213391873171913/12500000000000000000)
  centralHi := (48888341426997075061/20000000000000000000)
  directionLo := (249482272639815115601/100000000000000000000)
  directionHi := (124741136319907557801/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree026.table
  base := (-974547254522370109089145890318325119839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-8878798917647012772937582225171070991000000000000)
      constant := (61019073196089142085983115880922000010547741458641) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree026.table
  base := (-7848337374837967974784758553861503959/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-8887934615020634736628173921535648491000000000000)
      constant := (61142376485862555766397012398192942401049549115125) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249482272639815115601/100000000000000000000)
  centralHi := (124741136319907557801/50000000000000000000)
  directionLo := (63605748824294630087/25000000000000000000)
  directionHi := (254422995297178520349/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree027.table
  base := (-1628684081430715104525769717776411355219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-1024375301748404397702537851738057799000000000000)
      constant := (7276656813654000163182292704805243572492646349429) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree027.table
  base := (-1634327316909766429659742264169195743017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-1025429420676130008897606124395509049000000000000)
      constant := (7291508360727900374182254199962300539686457968047) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63605748824294630087/25000000000000000000)
  centralHi := (254422995297178520349/100000000000000000000)
  directionLo := (259269583079946354809/100000000000000000000)
  directionHi := (25926958307994635481/10000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree028.table
  base := (-445497259780111957018678139726223811019/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-9559956513824266385708099106113969391000000000000)
      constant := (70170548126096969837423778012737808340538982725305) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree028.table
  base := (-558096031852709354029764725057781311521/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80081414939314682489336673786571462500000000000)
      linear := (-2392448739287426355882184079395878597750000000000)
      constant := (17578722815793277446172628122240727196288885345199) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259269583079946354809/100000000000000000000)
  centralHi := (25926958307994635481/10000000000000000000)
  directionLo := (264027219969665792083/100000000000000000000)
  directionHi := (66006804992416448021/25000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree029.table
  base := (-2776386762654745738520343128029103797797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-9900535311912893192093357546585418591000000000000)
      constant := (75058161619207012562005284691804461419594415787243) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree029.table
  base := (-27806332938688940209049361732005094253/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80081414939314682489336673786571462500000000000)
      linear := (-2477681282053560191744754378901861835250000000000)
      constant := (18803377217046420072472453878745841007294731917675) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264027219969665792083/100000000000000000000)
  centralHi := (66006804992416448021/25000000000000000000)
  directionLo := (268700630924773543783/100000000000000000000)
  directionHi := (33587578865596692973/12500000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree030.table
  base := (-204994951976441360562430111593339468447/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4448967496628593471629815210365081250000000000)
      linear := (-142237695972243333312202999820234274875000000000)
      constant := (1113199956017520813089252778022899443484414494354) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree030.table
  base := (-820899391815291623920553237363543346597/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8897934993257186943259630420730162500000000000)
      linear := (-284768202757743780845258297600871674750000000000)
      constant := (2231029966958096381537566108512320963855271983827) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268700630924773543783/100000000000000000000)
  centralHi := (33587578865596692973/12500000000000000000)
  directionLo := (13664706842248066517/5000000000000000000)
  directionHi := (273294136844961330341/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree031.table
  base := (-3741868808127891577622008003203036620091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-10581692908090146804863874427528316991000000000000)
      constant := (85445287673768559653668186956964424906194813679029) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree031.table
  base := (-3745052143988259952058724417656760839267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-10592585470343311453879579911655313241000000000000)
      constant := (85623640141028399459748778434194830095766249916173) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13664706842248066517/5000000000000000000)
  centralHi := (273294136844961330341/100000000000000000000)
  directionLo := (69452925338090300919/25000000000000000000)
  directionHi := (277811701352361203677/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree032.table
  base := (-4165396832125306426329592444783527238413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-10922271706178773611249132867999766191000000000000)
      constant := (90941192046923281246128551049763148444496324463747) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree032.table
  base := (-4168149492462595284065191355575298172651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-10933515641407846797329861109679246191000000000000)
      constant := (91131555374134643101654899000441591810700008145669) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69452925338090300919/25000000000000000000)
  centralHi := (277811701352361203677/100000000000000000000)
  directionLo := (282256970831110942673/100000000000000000000)
  directionHi := (141128485415555471337/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree033.table
  base := (-4553144661367911897275818788548203649643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-1251427833807488935292710145385690599000000000000)
      constant := (10737415328123424502816680597244805150349211194013) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree033.table
  base := (-1138880764606678824797026353004889146897/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8897934993257186943259630420730162500000000000)
      linear := (-313179050346455059466115064102866087250000000000)
      constant := (2689984906109117245623588578784261565526325461127) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282256970831110942673/100000000000000000000)
  centralHi := (141128485415555471337/50000000000000000000)
  directionLo := (143316654438009833823/50000000000000000000)
  directionHi := (286633308876019667647/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree034.table
  base := (-4907319972627149334122867802340721724631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-11603429302356027224019649748942664591000000000000)
      constant := (102530778659490036604284252005279353405265149827289) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree034.table
  base := (-4909373488194169823609046323249333694223/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-11615375983536917484230423505727112091000000000000)
      constant := (102746200797396491669940544531088812934747195567137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (143316654438009833823/50000000000000000000)
  centralHi := (286633308876019667647/100000000000000000000)
  directionLo := (72735956518972090533/25000000000000000000)
  directionHi := (290943826075888362133/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree035.table
  base := (-5229768575567289555428959317869610780949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-11944008100444654030404908189414113791000000000000)
      constant := (108622355397735830574549625932879234532457500052731) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree035.table
  base := (-1307885091103450588603229002513468050587/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80081414939314682489336673786571462500000000000)
      linear := (-2989076538650363206920176175937761260250000000000)
      constant := (27212708093177748417854807762593984482279902727253) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72735956518972090533/25000000000000000000)
  centralHi := (290943826075888362133/100000000000000000000)
  directionLo := (295191405881231336591/100000000000000000000)
  directionHi := (18449462867576958537/6250000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree036.table
  base := (-2761017103491499202374419885523290131449/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17795869986514373886519260841460325000000000000)
      linear := (-682477049918515602043898146104753499500000000000)
      constant := (6383925905840966733029278295042299086327888651359) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree036.table
  base := (-1380890481052580483238904920078889340923/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8897934993257186943259630420730162500000000000)
      linear := (-341589897935166338086971830604860499750000000000)
      constant := (3198682009440353802008775965124950146812229540493) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295191405881231336591/100000000000000000000)
  centralHi := (18449462867576958537/6250000000000000000)
  directionLo := (299378727167778138721/100000000000000000000)
  directionHi := (149689363583889069361/50000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree037.table
  base := (-723176043055242326363443447020040857747/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40040707469657341244668336893285731250000000000)
      linear := (-1578145712077738455396928133794626523875000000000)
      constant := (15174380068739219844633402866322384613153509411293) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree037.table
  base := (-1157344960038873972602167476328637948017/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-12638166496730523514581267099798910941000000000000)
      constant := (121650692383655211663006068890130110914485175537115) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299378727167778138721/100000000000000000000)
  centralHi := (149689363583889069361/50000000000000000000)
  directionLo := (75877070999355604853/25000000000000000000)
  directionHi := (303508283997422419413/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree038.table
  base := (-6020971726383865704850546207500304024133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-12965744494710534449560683510828461391000000000000)
      constant := (128074916764441896609013279071484992081341579508427) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree038.table
  base := (-3011052736156988131576932429504139027111/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160162829878629364978673347573142925000000000000)
      linear := (-6489548333897529429015774148911421945500000000000)
      constant := (64172346674241204931209837721990223343468082918409) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75877070999355604853/25000000000000000000)
  centralHi := (303508283997422419413/100000000000000000000)
  directionLo := (307582402990680049649/100000000000000000000)
  directionHi := (6151648059813600993/2000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree039.table
  base := (-6229628975992271451507305967814437714301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-1478480365866573472882882439033323399000000000000)
      constant := (14994425006732243157604637331847088941651806936891) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree039.table
  base := (-778825603548035205413514609145702106957/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4448967496628593471629815210365081250000000000)
      linear := (-185000372761938808353914298553427456125000000000)
      constant := (1878251212311998559007181357533884143756921956587) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307582402990680049649/100000000000000000000)
  centralHi := (6151648059813600993/2000000000000000000)
  directionLo := (62320651730861154473/20000000000000000000)
  directionHi := (155801629327152886183/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree040.table
  base := (-6412137487232201886844271881945160057369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-13646902090887788062331200391771359791000000000000)
      constant := (142019372025452978997740228610037560491906878630711) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree040.table
  base := (-3206488495958129024543321480985271224801/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160162829878629364978673347573142925000000000000)
      linear := (-6830478504962064772466055346935354895500000000000)
      constant := (71159241241732466005822756007311175572003137281519) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62320651730861154473/20000000000000000000)
  centralHi := (155801629327152886183/50000000000000000000)
  directionLo := (315572886950769690003/100000000000000000000)
  directionHi := (78893221737692422501/25000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree041.table
  base := (-6569131534150411732322579922856418364911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-13987480888976414868716458832242808991000000000000)
      constant := (149283228198264495962854955229391984355911737676609) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree041.table
  base := (-3284926689178556510139884500555594316967/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160162829878629364978673347573142925000000000000)
      linear := (-7000943590494332444191195945947321370500000000000)
      constant := (74798775481780597833535477242016896036672418302473) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315572886950769690003/100000000000000000000)
  centralHi := (78893221737692422501/25000000000000000000)
  directionLo := (319493197349966042383/100000000000000000000)
  directionHi := (19968324834372877649/6250000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree042.table
  base := (-6701142401422396004012444834230417178281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-1592006631896115741677968585857139799000000000000)
      constant := (17415679734888358527674608258530525310732064449071) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree042.table
  base := (-335088138879847219675665649974483432483/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8897934993257186943259630420730162500000000000)
      linear := (-398411593112588895328685363608849324750000000000)
      constant := (4363083834933021046401556844054052813819761262265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319493197349966042383/100000000000000000000)
  centralHi := (19968324834372877649/6250000000000000000)
  directionLo := (161682991782813561221/50000000000000000000)
  directionHi := (323365983565627122443/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree043.table
  base := (-3404307599574425351947119159529946912493/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160162829878629364978673347573142925000000000000)
      linear := (-7334319242576834240743487856592853695500000000000)
      constant := (82196404534623778477101573030119423259296826095267) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree043.table
  base := (-3404574062758206856538404325230030749739/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160162829878629364978673347573142925000000000000)
      linear := (-7341873761558867787641477143971254320500000000000)
      constant := (82369326845752211270890753931190508870042880396741) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161682991782813561221/50000000000000000000)
  centralHi := (323365983565627122443/100000000000000000000)
  directionLo := (327192933147747724873/100000000000000000000)
  directionHi := (163596466573873862437/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree044.table
  base := (-6891922913102863857647051763943053764829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-15009217283242295287872234153657156591000000000000)
      constant := (172238108824140353926686560182473786984769023510451) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree044.table
  base := (-1378476103097522228878909119918453494613/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-15024677694182270918733235485966441591000000000000)
      constant := (172600265108396304272117762913089165030399170957735) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327192933147747724873/100000000000000000000)
  centralHi := (163596466573873862437/50000000000000000000)
  directionLo := (82743909019141551547/25000000000000000000)
  directionHi := (330975636076566206189/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree045.table
  base := (-868922268619226624004330226296914490281/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4448967496628593471629815210365081250000000000)
      linear := (-213191612240707251309131841585119524875000000000)
      constant := (2503845201416812418143420133594804894169895841071) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree045.table
  base := (-6951770908030537912373766932593728121519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-1707289762805200695798168520443374949000000000000)
      constant := (20072854531793410559010181445274652349359850732729) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82743909019141551547/25000000000000000000)
  centralHi := (330975636076566206189/100000000000000000000)
  directionLo := (167357796241128751349/50000000000000000000)
  directionHi := (334715592482257502699/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree046.table
  base := (-6987242952115687626542692014070749330183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-15690374879419548900642751034600054991000000000000)
      constant := (188508909988692181404078422475883838099992080638377) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree046.table
  base := (-109180936248976575825558716068706258743/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40040707469657341244668336893285731250000000000)
      linear := (-1963317254538917700704224735251788436375000000000)
      constant := (23613099419080232740595168576503258266632360392136) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167357796241128751349/50000000000000000000)
  centralHi := (334715592482257502699/100000000000000000000)
  directionLo := (84603554899162539907/25000000000000000000)
  directionHi := (338414219596650159629/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree047.table
  base := (-1749934255262304949699436439218309868739/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80081414939314682489336673786571462500000000000)
      linear := (-4007738419377043926757002368767876047750000000000)
      constant := (49233540291571010396653060831920903378521749357741) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree047.table
  base := (-7000026010334407151020138820204993407063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-16047468207375876949084079080038240441000000000000)
      constant := (197347465333741048577933285724629424921962162763097) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (84603554899162539907/25000000000000000000)
  centralHi := (338414219596650159629/100000000000000000000)
  directionLo := (342072858028331208027/100000000000000000000)
  directionHi := (85518214507082802007/25000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree048.table
  base := (-6989044578835263144859595110242100304651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-1819059163955200279268140879504772599000000000000)
      constant := (22839168038205550445837942697957870885998347583741) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree048.table
  base := (-6989292328228654094148240533342277486767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-1820933153160045810281595586451352599000000000000)
      constant := (22887067288490271335354978133574862612137237274297) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342072858028331208027/100000000000000000000)
  centralHi := (85518214507082802007/25000000000000000000)
  directionLo := (345692777439928473079/100000000000000000000)
  directionHi := (8642319435998211827/2500000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree049.table
  base := (-1391064024754772846484478725338377829307/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-16712111273685429319798526356014402591000000000000)
      constant := (214363883270387210450923626252347858219327962694665) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree049.table
  base := (-3477766220938680688173529645664381680241/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160162829878629364978673347573142925000000000000)
      linear := (-8364664274752473817992320738043053170500000000000)
      constant := (107406568186371838273901848885422532920270173366879) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (345692777439928473079/100000000000000000000)
  centralHi := (8642319435998211827/2500000000000000000)
  directionLo := (349275181695741161841/100000000000000000000)
  directionHi := (174637590847870580921/50000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree050.table
  base := (-1379738648623377932729115896295702705481/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-17052690071774056126183784796485851791000000000000)
      constant := (223368206634430912165944438357352276110105836092195) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree050.table
  base := (-689887513389216667579127273361773746697/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160162829878629364978673347573142925000000000000)
      linear := (-8535129360284741489717461337055019645500000000000)
      constant := (111917995384611935430349057981052139163295012431715) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349275181695741161841/100000000000000000000)
  centralHi := (174637590847870580921/50000000000000000000)
  directionLo := (352821213538888678341/100000000000000000000)
  directionHi := (176410606769444339171/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree051.table
  base := (-6819272643546282827561684048769367629829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-1932585429984742548063227026328588999000000000000)
      constant := (25840602885611548303842077102925314493940688493939) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree051.table
  base := (-1704857103838577624459848879053615605029/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8897934993257186943259630420730162500000000000)
      linear := (-483644135878722731191255663114832562250000000000)
      constant := (6473669796713654214891539047709687852042573837139) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (352821213538888678341/100000000000000000000)
  centralHi := (176410606769444339171/50000000000000000000)
  directionLo := (89082989712372686121/25000000000000000000)
  directionHi := (71266391769898148897/20000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree052.table
  base := (-3358574763309452656580800639932153227759/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160162829878629364978673347573142925000000000000)
      linear := (-8866923833975654869477150838714375095500000000000)
      constant := (120977746952905345419147849901123004003262022285121) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree052.table
  base := (-6717282886928877188677040473034422632497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-17752119062698553666335485070157905191000000000000)
      constant := (242461455049472156024218280596068292831982903056543) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89082989712372686121/25000000000000000000)
  centralHi := (71266391769898148897/20000000000000000000)
  directionLo := (179904225264428021829/50000000000000000000)
  directionHi := (359808450528856043659/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree053.table
  base := (-1318480083249413992802600471445456174457/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-18074426466039936545339560117900199391000000000000)
      constant := (251538370691559818944788897640886666000011600708915) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree053.table
  base := (-6592514553813528613815344557216373004237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-18093049233763089009785766268181838141000000000000)
      constant := (252063978393210107880318425828146693395432163441603) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (179904225264428021829/50000000000000000000)
  centralHi := (359808450528856043659/100000000000000000000)
  directionLo := (363251672049059298801/100000000000000000000)
  directionHi := (181625836024529649401/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree054.table
  base := (-1611272381913707519761045882967262166989/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8897934993257186943259630420730162500000000000)
      linear := (-511527924003571204214578293288101349750000000000)
      constant := (7258722860346054825151915691075383071684170555499) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree054.table
  base := (-1289037436750554502919484711178948023421/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-2048219933869736039248449718467307899000000000000)
      constant := (29095516621116246617645328474325185028932694134055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363251672049059298801/100000000000000000000)
  centralHi := (181625836024529649401/50000000000000000000)
  directionLo := (91665640175619515739/25000000000000000000)
  directionHi := (366662560702478062957/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree055.table
  base := (-3137635376275120877520184691426164626449/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160162829878629364978673347573142925000000000000)
      linear := (-9377792031108595079055038499421548895500000000000)
      constant := (135641211377776215498426323593555737063030111767231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree055.table
  base := (-251014171306788831768940179158661329769/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-18774909575892159696686328664229704041000000000000)
      constant := (271848440847415917433280275123529821057276313157775) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91665640175619515739/25000000000000000000)
  centralHi := (366662560702478062957/100000000000000000000)
  directionLo := (185021005290858456613/50000000000000000000)
  directionHi := (370042010581716913227/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree056.table
  base := (-3041494661495492559394424139104137865237/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160162829878629364978673347573142925000000000000)
      linear := (-9548081430152908482247667719657273495500000000000)
      constant := (140721773272984949528541391907109142090879924100603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree056.table
  base := (-6083060750223973702352799592826537416833/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-19115839746956695040136609862253636991000000000000)
      constant := (282030328843103338337467377405711430577239870779727) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (185021005290858456613/50000000000000000000)
  centralHi := (370042010581716913227/100000000000000000000)
  directionLo := (373390875316765840291/100000000000000000000)
  directionHi := (93347718829191460073/25000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree057.table
  base := (-1467070801546638158477055077921705638419/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8897934993257186943259630420730162500000000000)
      linear := (-539909490510956771413349829994055449750000000000)
      constant := (8105482628400412854322501700213086727806679720629) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree057.table
  base := (-1467086066847051193752570490987744017063/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8897934993257186943259630420730162500000000000)
      linear := (-540465831056145288432969196118821387250000000000)
      constant := (8122369277902579630189851926319948813561923039233) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (373390875316765840291/100000000000000000000)
  centralHi := (93347718829191460073/25000000000000000000)
  directionLo := (94177492648284088079/25000000000000000000)
  directionHi := (376709970593136352317/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree058.table
  base := (-5631184273935642726812529412531245387749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-19777320456483070577265852320257445391000000000000)
      constant := (302343890429729091272587030555383166933708815621931) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree058.table
  base := (-1126247291921621775835971773100428730031/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-19797700089085765727037172258301502891000000000000)
      constant := (302973319904389333713801362561917730721983812749445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94177492648284088079/25000000000000000000)
  centralHi := (376709970593136352317/100000000000000000000)
  directionLo := (76000015294404444481/20000000000000000000)
  directionHi := (190000038236011111203/50000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree059.table
  base := (-5371719283260759078551279788097861183819/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-20117899254571697383651110760728894591000000000000)
      constant := (313083080069520921011144822141719168812506614468261) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree059.table
  base := (-5371763871988931929872794556373910818497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-20138630260150301070487453456325435841000000000000)
      constant := (313734392754477189421306602943506206230825654390543) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76000015294404444481/20000000000000000000)
  centralHi := (190000038236011111203/50000000000000000000)
  directionLo := (383261939531182535957/100000000000000000000)
  directionHi := (191630969765591267979/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree060.table
  base := (-5089910698839153821206740830187690684779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-2273164228073369354448485466800038199000000000000)
      constant := (36001659096996690347595485878971095513053174719389) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree060.table
  base := (-5089948787002706263863673319602634248743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-2275506714579426268215303850483263199000000000000)
      constant := (36076500108953232684581987067693155039490638762113) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383261939531182535957/100000000000000000000)
  centralHi := (191630969765591267979/50000000000000000000)
  directionLo := (48312034355399111757/12500000000000000000)
  directionHi := (386496274843192894057/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree061.table
  base := (-2392888691422699414854045055254726943001/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160162829878629364978673347573142925000000000000)
      linear := (-10399528425374475498210813820835896495500000000000)
      constant := (167569718021251823394462324129390112148254885387319) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree061.table
  base := (-4785809910238866634055660209234001445887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-20820490602279371757388015852373301741000000000000)
      constant := (335835634866456694922924399711200998875609376827953) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48312034355399111757/12500000000000000000)
  centralHi := (386496274843192894057/100000000000000000000)
  directionLo := (77940753561182863897/20000000000000000000)
  directionHi := (194851883902957159743/50000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree062.table
  base := (-178373406946157100333361312650395344447/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-21139635648837577802806886082143242191000000000000)
      constant := (346456584351199442491100416315361618634750241714825) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree062.table
  base := (-55742036819563797769973455767392095349/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40040707469657341244668336893285731250000000000)
      linear := (-2645177596667988387604787131299654336375000000000)
      constant := (43396973281881875827213402799035517089234473463310) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77940753561182863897/20000000000000000000)
  centralHi := (194851883902957159743/50000000000000000000)
  directionLo := (78577015167690625047/20000000000000000000)
  directionHi := (98221268959613281309/25000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree063.table
  base := (-20552986856824415593891158259495041913/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4448967496628593471629815210365081250000000000)
      linear := (-298336311762863952905446451702981824875000000000)
      constant := (4971755137369317021561261643641455176939024389575) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree063.table
  base := (-164424843103609605364575647326666365827/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-2389150104934271382698730916491240849000000000000)
      constant := (39856549810877430507172388618696566080902922468925) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78577015167690625047/20000000000000000000)
  centralHi := (98221268959613281309/25000000000000000000)
  directionLo := (633665327927197901/160000000000000000)
  directionHi := (198020414977249344063/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree064.table
  base := (-1869787572600543207928968334006373937299/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160162829878629364978673347573142925000000000000)
      linear := (-10910396622507415707788701481543070295500000000000)
      constant := (184834393429525974585130505466088304245782066428381) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree064.table
  base := (-186979768820711323412522351314315215783/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80081414939314682489336673786571462500000000000)
      linear := (-5460820278868244446934714861611275147750000000000)
      constant := (92608778811210953157774280719600505039661950723885) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (633665327927197901/160000000000000000)
  centralHi := (198020414977249344063/50000000000000000000)
  directionLo := (399171636223704184961/100000000000000000000)
  directionHi := (199585818111852092481/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree065.table
  base := (-1673138937692081379256321200238277287163/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160162829878629364978673347573142925000000000000)
      linear := (-11080686021551729110981330701778794895500000000000)
      constant := (190781915192108643387577740970133048274739377514997) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree065.table
  base := (-1673147568609213714641968715560844658197/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160162829878629364978673347573142925000000000000)
      linear := (-11092105643268756565594570322234516770500000000000)
      constant := (191177141133851364881639955608299405680602178254843) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399171636223704184961/100000000000000000000)
  centralHi := (199585818111852092481/50000000000000000000)
  directionLo := (201139038565348067481/50000000000000000000)
  directionHi := (402278077130696134963/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree066.table
  base := (-2930713440055681939613421915296782448069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-2500216760132453892038657760447670999000000000000)
      constant := (43739055152660697321860443756627762725408124473779) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree066.table
  base := (-2930728165214107558668801217676140058273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-2502793495289116497182157982499218499000000000000)
      constant := (43829605034690580964747314651710180482135548244343) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201139038565348067481/50000000000000000000)
  centralHi := (402278077130696134963/100000000000000000000)
  directionLo := (405360712840343458927/100000000000000000000)
  directionHi := (25335044552521466183/6250000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree067.table
  base := (-2492888456099350818615215948559147178841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-22842529639280711834733178284500488191000000000000)
      constant := (405931781391233123466922354839909003943262569420279) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree067.table
  base := (-498580202952667069197232533106280090337/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-22866071628666583818089703040516899441000000000000)
      constant := (406771600973851110995391609616615959039898004537515) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405360712840343458927/100000000000000000000)
  centralHi := (25335044552521466183/6250000000000000000)
  directionLo := (51052510297133723567/12500000000000000000)
  directionHi := (408420082377069788537/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree068.table
  base := (-508202120322107814758082177996906722803/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80081414939314682489336673786571462500000000000)
      linear := (-5795777109342334660279609181242984347750000000000)
      constant := (104601170637301359251398966113852693093987682284157) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree068.table
  base := (-2032819190060038187516514202262246994419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-23207001799731119161539984238540832391000000000000)
      constant := (419269746393568680831690107702093733703345730049661) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51052510297133723567/12500000000000000000)
  centralHi := (408420082377069788537/100000000000000000000)
  directionLo := (411456704725240263913/100000000000000000000)
  directionHi := (205728352362620131957/50000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree069.table
  base := (-1550478183983188030718140019134177534001/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-2613743026161996160833743907271487399000000000000)
      constant := (47896688602553148154476004795870004207924054879591) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree069.table
  base := (-775243656782151519201747775936549068639/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17795869986514373886519260841460325000000000000)
      linear := (-1308218442821980805832792524253598074500000000000)
      constant := (23997826620573609432737711335044800289503999680649) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (411456704725240263913/100000000000000000000)
  centralHi := (205728352362620131957/50000000000000000000)
  directionLo := (414471079856984274239/100000000000000000000)
  directionHi := (1295222124553075857/312500000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree070.table
  base := (-522950742799171502144741943487801125893/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160162829878629364978673347573142925000000000000)
      linear := (-11932133016773296126944476802957417895500000000000)
      constant := (221964161987826307285514332797749295493785958169867) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree070.table
  base := (-1045909267382335838544352167277107778627/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-23888862141860189848440546634588698291000000000000)
      constant := (444844997287638789708676567224368593512945158772013) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (414471079856984274239/100000000000000000000)
  centralHi := (1295222124553075857/312500000000000000)
  directionLo := (417463689693218369449/100000000000000000000)
  directionHi := (8349273793864367389/2000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree071.table
  base := (-51908168021850413341185228655828757561/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 515205000000000000000000000000000000000000000
      center := (9067608)
      previous := (4533804)
      next := (4533804)
      square := (31772035286377576865438077280925000000000000)
      linear := (-2400797940055070329326940294225975500000000000)
      constant := (45326230955780893022361357119439371744960784995) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree071.table
  base := (-25954415597305725610702366680886752677/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 257602500000000000000000000000000000000000000
      center := (4533804)
      previous := (2266902)
      next := (2266902)
      square := (15886017643188788432719038640462500000000000)
      linear := (-1201636198815945506441719293424550250000000000)
      constant := (22709883904579696408176860292962285240587046215) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417463689693218369449/100000000000000000000)
  centralHi := (8349273793864367389/2000000000000000000)
  directionLo := (42043499900310011981/10000000000000000000)
  directionHi := (420434999003100119811/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree072.table
  base := (29978464966162571769149987709588959707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-2727269292191538429628830054095303799000000000000)
      constant := (52246933949689852759394742172109554718442414318163) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree072.table
  base := (29972814355757959754749698485954442011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-2730080275998806726149012114515173799000000000000)
      constant := (52354687004538141920701574744038623683421589636499) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42043499900310011981/10000000000000000000)
  centralHi := (420434999003100119811/100000000000000000000)
  directionLo := (423385456246666414009/100000000000000000000)
  directionHi := (42338545624666641401/10000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree073.table
  base := (601276625323311163793293007952042153829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-24886002427812472673044728927329183391000000000000)
      constant := (483658357921246710822574186816270054587261950398549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree073.table
  base := (7515897644166087878635558491490355427/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40040707469657341244668336893285731250000000000)
      linear := (-3113956581881724484848923778582562142625000000000)
      constant := (60581906007456319659175940319764814558215232287870) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423385456246666414009/100000000000000000000)
  centralHi := (42338545624666641401/10000000000000000000)
  directionLo := (426315494364981956239/100000000000000000000)
  directionHi := (5328943679562274453/1250000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree074.table
  base := (1194810847956100981230795383208109762951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-25226581225901099479429987367800632591000000000000)
      constant := (497286916603904488444837423928233343394782623548631) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree074.table
  base := (597403373883622329781068491921279070133/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160162829878629364978673347573142925000000000000)
      linear := (-12626291413059165611120835713342215045500000000000)
      constant := (249155646552461296482681008605690023244011160817573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (426315494364981956239/100000000000000000000)
  centralHi := (5328943679562274453/1250000000000000000)
  directionLo := (85845106304347959321/20000000000000000000)
  directionHi := (214612765760869898303/50000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree075.table
  base := (1810579492226325172626687637998426138553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-2840795558221080698423916200919120199000000000000)
      constant := (56789786749220647475564346856040319407516738510177) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree075.table
  base := (181057600044286913266765513558498594011/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17795869986514373886519260841460325000000000000)
      linear := (-1421861833176825920316219590261575724500000000000)
      constant := (28453350962990284238817535116417710816403379022495) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85845106304347959321/20000000000000000000)
  centralHi := (214612765760869898303/50000000000000000000)
  directionLo := (432115971799910591349/100000000000000000000)
  directionHi := (8642319435998211827/2000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree076.table
  base := (2448581179802895123292370060810951553857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-25907738822078353092200504248743530991000000000000)
      constant := (525121849622544649656788848882171257582926395829617) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree076.table
  base := (2448578206636674241355254819870079035809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-25934443168247401909142233822732295991000000000000)
      constant := (526202320038415215604908056321596417981015056446929) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432115971799910591349/100000000000000000000)
  centralHi := (8642319435998211827/2000000000000000000)
  directionLo := (43498720585672655747/10000000000000000000)
  directionHi := (434987205856726557471/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree077.table
  base := (1554407376354066983891164405120677778413/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160162829878629364978673347573142925000000000000)
      linear := (-13124158810083489949292881344607490095500000000000)
      constant := (269664111320546490137813581142068378090944853276253) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree077.table
  base := (3108812221538890087815338588000480098399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-26275373339311937252592515020756228941000000000000)
      constant := (540437300624044717300236648088097634162358241180719) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43498720585672655747/10000000000000000000)
  centralHi := (434987205856726557471/100000000000000000000)
  directionLo := (437839611540005924089/100000000000000000000)
  directionHi := (43783961154000592409/10000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree078.table
  base := (3791279238079735862585248490287716696313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-2954321824250622967219002347742936599000000000000)
      constant := (61525244365921917995041615937135967081087137274017) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree078.table
  base := (1895638541769042570586368866935213320683/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17795869986514373886519260841460325000000000000)
      linear := (-1478683528354248477557933123265564549500000000000)
      constant := (30825847699512450125481420936843819126592146821347) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (437839611540005924089/100000000000000000000)
  centralHi := (43783961154000592409/10000000000000000000)
  directionLo := (27542097154285670373/6250000000000000000)
  directionHi := (440673554468570725969/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree079.table
  base := (4495973818572134083780135504233143254963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-26929475216344233511356279570157878591000000000000)
      constant := (568318779154603947705860495559286402514552732756803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree079.table
  base := (899194396979842524192153229501183051439/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-26957233681441007939493077416804094841000000000000)
      constant := (569486193520391812798496954849638820821657831804795) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27542097154285670373/6250000000000000000)
  centralHi := (440673554468570725969/100000000000000000000)
  directionLo := (443489388579282077187/100000000000000000000)
  directionHi := (110872347144820519297/25000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree080.table
  base := (1044579561498754651399692562334617468383/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-27270054014432860317741538010629327791000000000000)
      constant := (583102961868325061973582939082287644114296046379115) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree080.table
  base := (1305724061784510817923418585414309171013/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80081414939314682489336673786571462500000000000)
      linear := (-6824540963126385820735839653707006947750000000000)
      constant := (146075026264780750538505737922809958435534657036853) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (443489388579282077187/100000000000000000000)
  centralHi := (110872347144820519297/25000000000000000000)
  directionLo := (223143728321505001799/50000000000000000000)
  directionHi := (446287456643010003599/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree081.table
  base := (5972050627921746957825579194284966386863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-3067848090280165236014088494566752999000000000000)
      constant := (66453305237198858168101702345463096456602663408967) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree081.table
  base := (5972049300339018323175969066283036980247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-3071010447063342069599293312539106749000000000000)
      constant := (66589665879042957048478241113498349925040100279023) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223143728321505001799/50000000000000000000)
  centralHi := (446287456643010003599/100000000000000000000)
  directionLo := (449068090751667208081/100000000000000000000)
  directionHi := (224534045375833604041/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree082.table
  base := (1348686359031384597333744002690862275831/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-27951211610610113930512054891572226191000000000000)
      constant := (613249134702230816704446343573783480579749151699555) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree082.table
  base := (1685857666446111059213327533617895955149/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80081414939314682489336673786571462500000000000)
      linear := (-6995006048658653492460980252718973422750000000000)
      constant := (153626714207130616950388391928980431518624235377469) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449068090751667208081/100000000000000000000)
  centralHi := (224534045375833604041/50000000000000000000)
  directionLo := (90366322555653153487/20000000000000000000)
  directionHi := (112957903194566441859/25000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree083.table
  base := (376852045099239546282309049869143053903/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80081414939314682489336673786571462500000000000)
      linear := (-7072947602174685184224328333010918847750000000000)
      constant := (157152781089782259575811134032624493348161005474715) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree083.table
  base := (7537039941364394955909604385254182604033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-28320954365699149313294202208899826641000000000000)
      constant := (629899696601662734631145573628281313301928610503473) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90366322555653153487/20000000000000000000)
  centralHi := (112957903194566441859/25000000000000000000)
  directionLo := (227289167405900461453/50000000000000000000)
  directionHi := (454578334811800922907/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree084.table
  base := (4176438803146489412223108297928646314343/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17795869986514373886519260841460325000000000000)
      linear := (-1590687178154853752404587320695284699500000000000)
      constant := (35786984218210059337833673385422826154202334468287) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree084.table
  base := (83528767893218226281343591910901881843/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8897934993257186943259630420730162500000000000)
      linear := (-796163459354546796020680094636771099750000000000)
      constant := (17930153112649066063991798789671878385688914394675) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227289167405900461453/50000000000000000000)
  centralHi := (454578334811800922907/100000000000000000000)
  directionLo := (114327139892156310253/25000000000000000000)
  directionHi := (457308559568625241013/100000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree085.table
  base := (9190941620668337981418180040601116851641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-28972948004875994349667830212986573791000000000000)
      constant := (659912909258895985892427138370832635034491608956521) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree085.table
  base := (1838188185191766396372444619231670968947/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-29002814707828220000194764604947692541000000000000)
      constant := (661264303042272291577898574270190536567485505579535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114327139892156310253/25000000000000000000)
  centralHi := (457308559568625241013/100000000000000000000)
  directionLo := (230011290390924039827/50000000000000000000)
  directionHi := (92004516156369615931/20000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree086.table
  base := (2512808175914225128504749568402771912017/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80081414939314682489336673786571462500000000000)
      linear := (-7328381700741155289013272163364505747750000000000)
      constant := (168963176056763858556023498630721236387774750376577) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree086.table
  base := (1256404014123756233338490684336474433491/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40040707469657341244668336893285731250000000000)
      linear := (-3667968109861594417955630725371453186375000000000)
      constant := (84654508679825997386407055125756161599277885846371) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (230011290390924039827/50000000000000000000)
  centralHi := (92004516156369615931/20000000000000000000)
  directionLo := (46272068357017824563/10000000000000000000)
  directionHi := (462720683570178245631/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree087.table
  base := (2733437663105182584918051847721387815871/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8897934993257186943259630420730162500000000000)
      linear := (-823725155584812443401065197053596449750000000000)
      constant := (19221808353524982462275989085833450241452795585239) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree087.table
  base := (2186750030055873461484525218225845998717/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-3298297227773032298566147444555062049000000000000)
      constant := (77044534571157422844687068295176258889704832066265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46272068357017824563/10000000000000000000)
  centralHi := (462720683570178245631/100000000000000000000)
  directionLo := (465403144787520860491/100000000000000000000)
  directionHi := (116350786196880215123/25000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree088.table
  base := (369952978017758487270023312203670250877/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40040707469657341244668336893285731250000000000)
      linear := (-3749335549892734346102950691800115173875000000000)
      constant := (88538762333740169704689811929790053457768920320948) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree088.table
  base := (5919247434869298015270533687526995876133/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160162829878629364978673347573142925000000000000)
      linear := (-15012802610510913015272804099509745695500000000000)
      constant := (354879264030194388547963047858708642000828079703573) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (465403144787520860491/100000000000000000000)
  centralHi := (116350786196880215123/25000000000000000000)
  directionLo := (468070233354541770277/100000000000000000000)
  directionHi := (234035116677270885139/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree089.table
  base := (398920827905329867823636749064371980287/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40040707469657341244668336893285731250000000000)
      linear := (-3791907899653812696901107996859046323875000000000)
      constant := (90603462247721995844961823996193447135243258793788) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree089.table
  base := (398920816568814507338783090099323982739/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40040707469657341244668336893285731250000000000)
      linear := (-3795816924010795171749486174630428042625000000000)
      constant := (90788652515649781712578043299557996158554073105036) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468070233354541770277/100000000000000000000)
  centralHi := (234035116677270885139/50000000000000000000)
  directionLo := (470722210573323456007/100000000000000000000)
  directionHi := (58840276321665432001/12500000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree090.table
  base := (13714664121405656078322416490158354961377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-3408426888368792042399346935038202199000000000000)
      constant := (82393099844446262102710348133304544933008091381193) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree090.table
  base := (1714332976640120923691943126971784318281/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4448967496628593471629815210365081250000000000)
      linear := (-426492577265984676631196813820379962375000000000)
      constant := (10320178989906492606887781829508755058480055810929) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (470722210573323456007/100000000000000000000)
  centralHi := (58840276321665432001/12500000000000000000)
  directionLo := (118339832606538633751/25000000000000000000)
  directionHi := (94671866085230907001/20000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree091.table
  base := (3671522020224748549871006556781137500333/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80081414939314682489336673786571462500000000000)
      linear := (-7754105198351938796994845213953817247750000000000)
      constant := (189610175118048335281819201510157850677615107583773) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree091.table
  base := (14686087818946303490339059308578402775317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-31048395734215432060896451793091290241000000000000)
      constant := (759989529452887712726859571223447979673072423983877) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118339832606538633751/25000000000000000000)
  centralHi := (94671866085230907001/20000000000000000000)
  directionLo := (118995459964854970141/25000000000000000000)
  directionHi := (95196367971883976113/20000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree092.table
  base := (627189531465931312638668923022508908821/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-31356999591496381994364639296286718191000000000000)
      constant := (775536103554258088318751722654173141030213752902525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree092.table
  base := (15679738064090225704993953020717919449649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-31389325905279967404346732991115223191000000000000)
      constant := (777119146620640980177885733897635188512714875631969) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118995459964854970141/25000000000000000000)
  centralHi := (95196367971883976113/20000000000000000000)
  directionLo := (478589979053489495291/100000000000000000000)
  directionHi := (119647494763372373823/25000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree093.table
  base := (16695614667439674365204912884076513516921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-3521953154398334311194433081862018599000000000000)
      constant := (88091567534357779375179089880970093620409607014689) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree093.table
  base := (16695614478373282470470534494629147145329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-3525584008482722527533001576571017349000000000000)
      constant := (88271304304452664434539923957330592058666700345561) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (478589979053489495291/100000000000000000000)
  centralHi := (119647494763372373823/25000000000000000000)
  directionLo := (481183981679440982959/100000000000000000000)
  directionHi := (6014799770993012287/1250000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree094.table
  base := (4433429290869156590101072406184797162263/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80081414939314682489336673786571462500000000000)
      linear := (-8009539296918408901783789044307404147750000000000)
      constant := (202576178301504755078009637942900536743043975328103) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree094.table
  base := (8866858501439913051459241356337495918889/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160162829878629364978673347573142925000000000000)
      linear := (-16035593123704519045623647693581544545500000000000)
      constant := (405978652890292087921724777640264784297987315144409) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481183981679440982959/100000000000000000000)
  centralHi := (6014799770993012287/1250000000000000000)
  directionLo := (12094101878584806607/2500000000000000000)
  directionHi := (483764075143392264281/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree095.table
  base := (9397022862277771241565917454638756687391/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160162829878629364978673347573142925000000000000)
      linear := (-16189367992881131206760207308850532895500000000000)
      constant := (413988959859288934052147757010749576866368123852271) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree095.table
  base := (9397022794078154621520551728058899672167/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160162829878629364978673347573142925000000000000)
      linear := (-16206058209236786717348788292593511020500000000000)
      constant := (414832923858241963823249289314452232390924709388727) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12094101878584806607/2500000000000000000)
  centralHi := (483764075143392264281/100000000000000000000)
  directionLo := (486330480819167614381/100000000000000000000)
  directionHi := (243165240409583807191/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree096.table
  base := (9938300154266394823140618502031584267521/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17795869986514373886519260841460325000000000000)
      linear := (-1817739710213938289994759614342917499500000000000)
      constant := (46991318184722550214598112164529819337333672410089) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree096.table
  base := (4969150048174408631325302620217912245999/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8897934993257186943259630420730162500000000000)
      linear := (-909806849709391910504107160644748749750000000000)
      constant := (23543537903505951550987540683797135532491694899591) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486330480819167614381/100000000000000000000)
  centralHi := (243165240409583807191/50000000000000000000)
  directionLo := (30555213391873171913/6250000000000000000)
  directionHi := (488883414269970750609/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree097.table
  base := (20981380880036545941697263322664915507649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-33059893581939516026290931498643964191000000000000)
      constant := (863902136006929953417308182830864146784030073129969) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree097.table
  base := (4196276156335099229665203443436578638731/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-33093976760602644121598138981234887941000000000000)
      constant := (865661856191684304638430697353898590357237287874055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30555213391873171913/6250000000000000000)
  centralHi := (488883414269970750609/100000000000000000000)
  directionLo := (98284617091938639189/20000000000000000000)
  directionHi := (245711542729846597973/50000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree098.table
  base := (86360888317907706463268633292597549307/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40040707469657341244668336893285731250000000000)
      linear := (-4175059047503517854084523742389426673875000000000)
      constant := (110269143218616509649860760436413099811333336994144) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree098.table
  base := (11054193662935010334751672400734308009761/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160162829878629364978673347573142925000000000000)
      linear := (-16717453465833589732524210089629410445500000000000)
      constant := (441974661348858202256989930483341890896765901116241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98284617091938639189/20000000000000000000)
  centralHi := (245711542729846597973/50000000000000000000)
  directionLo := (493949698954444149677/100000000000000000000)
  directionHi := (246974849477222074839/50000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree099.table
  base := (23257619871673654075970659794199525977313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-3749005686457418848784605375509651399000000000000)
      constant := (100066306282008568573560636438321698945860767203017) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree099.table
  base := (11628809900386101723210098899940783759233/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17795869986514373886519260841460325000000000000)
      linear := (-1876435394596206378249927854293486324500000000000)
      constant := (50134986890643325055509047453699706657660930888297) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (493949698954444149677/100000000000000000000)
  centralHi := (246974849477222074839/50000000000000000000)
  directionLo := (496463454114849309283/100000000000000000000)
  directionHi := (124115863528712327321/25000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree100.table
  base := (4885815649203458612272785132606110230489/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-34081629976205396445446706820058311791000000000000)
      constant := (919232968363515695411684649756357284278368688720045) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree100.table
  base := (4885815637165967136426976485347439157201/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-34116767273796250151948982575306686791000000000000)
      constant := (921103180182599216834738859174933595327959121414405) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (496463454114849309283/100000000000000000000)
  centralHi := (124115863528712327321/25000000000000000000)
  directionLo := (249482272639815115601/50000000000000000000)
  directionHi := (498964545279630231203/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree101.table
  base := (2562276251490147204923856640696727864013/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160162829878629364978673347573142925000000000000)
      linear := (-17211104387147011625915982630264880495500000000000)
      constant := (469030890608075307587417515414701493518740419849265) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree101.table
  base := (6405690615953495917137295338149290074421/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80081414939314682489336673786571462500000000000)
      linear := (-8614424361215196373849815943332654935250000000000)
      constant := (234992392785456320620185067961900394783982966289701) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (249482272639815115601/50000000000000000000)
  centralHi := (498964545279630231203/100000000000000000000)
  directionLo := (125363290485235661179/25000000000000000000)
  directionHi := (501453161940942644717/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree102.table
  base := (1341933633182299041622298361964700290041/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8897934993257186943259630420730162500000000000)
      linear := (-965632988121740279394922880583366949750000000000)
      constant := (26585644308009903876294020062938243842509224503845) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree102.table
  base := (3354834077535843723466502527883033459587/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4448967496628593471629815210365081250000000000)
      linear := (-483314272443407233872910346824368787375000000000)
      constant := (13319846345857757991432979088232039668872289089083) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (125363290485235661179/25000000000000000000)
  centralHi := (501453161940942644717/100000000000000000000)
  directionLo := (503929488911921417219/100000000000000000000)
  directionHi := (25196474445596070861/5000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree103.table
  base := (175480054249692105857997526703784761809/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40040707469657341244668336893285731250000000000)
      linear := (-4387920796308909608075310267684082423875000000000)
      constant := (122037151246718055076417831684378113799882197058580) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree103.table
  base := (7019202160788531498278985841385508446351/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80081414939314682489336673786571462500000000000)
      linear := (-8784889446747464045574956542344621410250000000000)
      constant := (244570319364029277200100390011312748549810905544031) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (503929488911921417219/100000000000000000000)
  centralHi := (25196474445596070861/5000000000000000000)
  directionLo := (1012787412973702813/200000000000000000)
  directionHi := (506393706486851406501/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree104.table
  base := (2933717055351473471675217969958806812479/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160162829878629364978673347573142925000000000000)
      linear := (-17721972584279951835493870290972054295500000000000)
      constant := (497851912933481835145957506873021167860732968945995) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree104.table
  base := (916786578821573087199066108521135830751/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40040707469657341244668336893285731250000000000)
      linear := (-4435060994756798940718763420925302323875000000000)
      constant := (124715824099955156929547868479133938735798647681724) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1012787412973702813/200000000000000000)
  centralHi := (506393706486851406501/100000000000000000000)
  directionLo := (508845990594357040697/100000000000000000000)
  directionHi := (254422995297178520349/50000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree105.table
  base := (1224790331028634350343161469261889864671/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-3976058218516503386374777669157284199000000000000)
      constant := (112811449195948405103350400035764789014064418610975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree105.table
  base := (7654939562305564764742140040921935464799/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8897934993257186943259630420730162500000000000)
      linear := (-995039392475525746366677460150731987250000000000)
      constant := (28260135636886939459304778868124627544237014588791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (508845990594357040697/100000000000000000000)
  centralHi := (254422995297178520349/50000000000000000000)
  directionLo := (255643256471989485373/50000000000000000000)
  directionHi := (511286512943978970747/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree106.table
  base := (31924571839341843763674735241799127450709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-36125102764737157283758257462887006991000000000000)
      constant := (1035094860659714102862467093445799152533800119093829) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree106.table
  base := (15962285908432138325162062860571246890323/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160162829878629364978673347573142925000000000000)
      linear := (-18081174150091731106325334881725142245500000000000)
      constant := (518598073918651163938498923743105518485512717876963) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (255643256471989485373/50000000000000000000)
  centralHi := (511286512943978970747/100000000000000000000)
  directionLo := (256857720583241695009/50000000000000000000)
  directionHi := (513715441166483390019/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree107.table
  base := (3325161123836421479657714159558853617941/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 226845000000000000000000000000000000000000000
      center := (3992472)
      previous := (1996236)
      next := (1996236)
      square := (13989241844582877542027543678325000000000000)
      linear := (-1592526926492522669671740584477179500000000000)
      constant := (46077355207981818162119482114434022148961826145) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree107.table
  base := (33251611219295574206575209744789669504449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (7984944)
      previous := (3992472)
      next := (3992472)
      square := (27978483689165755084055087356650000000000000)
      linear := (-3188337712572975592287619090005609000000000000)
      constant := (92341723078407138544065600275773750515747346681) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (256857720583241695009/50000000000000000000)
  centralHi := (513715441166483390019/100000000000000000000)
  directionLo := (129033234737057117939/25000000000000000000)
  directionHi := (516132938948228471757/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree108.table
  base := (17300438233874172847603742583865017023967/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17795869986514373886519260841460325000000000000)
      linear := (-2044792242273022827584931907990550299500000000000)
      constant := (59736461079937845550559177457261339889313194240503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree108.table
  base := (34600876451573023795993292160840285681297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-4093800960256948099950136906610905599000000000000)
      constant := (119715289109722801901364414945036020173487218708473) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129033234737057117939/25000000000000000000)
  centralHi := (516132938948228471757/100000000000000000000)
  directionLo := (518539166159892709619/100000000000000000000)
  directionHi := (25926958307994635481/5000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree109.table
  base := (1124136485102933408214577512590100817681/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40040707469657341244668336893285731250000000000)
      linear := (-4643354894875379712864254098037669323875000000000)
      constant := (136953240039634118783384582677505302486443523959044) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree109.table
  base := (35972367509574013005430271165812125416213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-37185138813377068243001513357522083341000000000000)
      constant := (1097847791223626584390167719604644280079875510818053) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (518539166159892709619/100000000000000000000)
  centralHi := (25926958307994635481/5000000000000000000)
  directionLo := (508724881816261371/97656250000000000)
  directionHi := (104186855795970328781/20000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree110.table
  base := (9341521100375147981415434723450109215097/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80081414939314682489336673786571462500000000000)
      linear := (-9371854489272916127324822806193200947750000000000)
      constant := (279047035546281189806844734596405096639012995094057) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree110.table
  base := (149464337559457668134415846907723105197/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160162829878629364978673347573142925000000000000)
      linear := (-18763034492220801793225897277773008145500000000000)
      constant := (559225477615631822337313409546368488813600894019625) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (508724881816261371/97656250000000000)
  centralHi := (104186855795970328781/20000000000000000000)
  directionLo := (261659215006236204963/50000000000000000000)
  directionHi := (523318430012472409927/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree111.table
  base := (9695506774863961194715486518594886823333/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8897934993257186943259630420730162500000000000)
      linear := (-1050777687643896980991237490701229249750000000000)
      constant := (31581749028931214438868639178101581694430551505197) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree111.table
  base := (19391013544793848890822702947657776133509/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17795869986514373886519260841460325000000000000)
      linear := (-2103722175305896607216781986309441624500000000000)
      constant := (63291505222718479294010954648967375840799777031181) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (261659215006236204963/50000000000000000000)
  centralHi := (523318430012472409927/100000000000000000000)
  directionLo := (525691768401579658627/100000000000000000000)
  directionHi := (131422942100394914657/25000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree112.table
  base := (2513762225921240115771971225378894337019/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40040707469657341244668336893285731250000000000)
      linear := (-4771071944158614765258726013214462773875000000000)
      constant := (144736298610626615429011676452437394803220971321878) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree112.table
  base := (4022019560637175319855264521405140559043/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160162829878629364978673347573142925000000000000)
      linear := (-19103964663285337136676178475796941095500000000000)
      constant := (580118103777700696015613710179510503557719335776415) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (525691768401579658627/100000000000000000000)
  centralHi := (131422942100394914657/25000000000000000000)
  directionLo := (264027219969665792083/50000000000000000000)
  directionHi := (528054439939331584167/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree113.table
  base := (41680589945346176730875083167037590140637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-38509154351357544928455066546187151391000000000000)
      constant := (1179030413714550183081613657186992868669759822046797) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree113.table
  base := (2605036871140667484185364400200560623607/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40040707469657341244668336893285731250000000000)
      linear := (-4818607437204401202100329768702226892625000000000)
      constant := (147677286983706098780553741378984989141857690158734) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264027219969665792083/50000000000000000000)
  centralHi := (528054439939331584167/100000000000000000000)
  directionLo := (132601646792682741973/25000000000000000000)
  directionHi := (530406587170730967893/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree114.table
  base := (4316321008961503654808739808066005950019/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17795869986514373886519260841460325000000000000)
      linear := (-2158318508302565096380018054814366699500000000000)
      constant := (66686835529404074593341465295457788099979150618855) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree114.table
  base := (43163210083599064221382683554129350141731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-4321087740966638328916991038626860899000000000000)
      constant := (133643706550092281563219720004569049563984070901979) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132601646792682741973/25000000000000000000)
  centralHi := (530406587170730967893/100000000000000000000)
  directionLo := (532748349493983238423/100000000000000000000)
  directionHi := (66593543686747904803/12500000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree115.table
  base := (22334028023088551882176817483705551974611/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160162829878629364978673347573142925000000000000)
      linear := (-19595155973767399270612791713565024895500000000000)
      constant := (610944133164235569027445665671777354230101111829091) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree115.table
  base := (8933611208215360412745567858548880365259/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-39230719839764280303703200545665681041000000000000)
      constant := (1224361396798250533421762334376534944095168229261895) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (532748349493983238423/100000000000000000000)
  centralHi := (66593543686747904803/12500000000000000000)
  directionLo := (535079863256901485431/100000000000000000000)
  directionHi := (66884982907112685679/12500000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree116.table
  base := (46195127813906438740960226955991464777099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-39530890745623425347610841867601498991000000000000)
      constant := (1243606094111558722738486281972605294643891269675419) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree116.table
  base := (11548781952395689840544565346125632404239/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80081414939314682489336673786571462500000000000)
      linear := (-9892912502707203911788370435922403497750000000000)
      constant := (311530602352834206666556993049588957702157126817759) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (535079863256901485431/100000000000000000000)
  centralHi := (66884982907112685679/12500000000000000000)
  directionLo := (268700630924773543783/50000000000000000000)
  directionHi := (537401261849547087567/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree117.table
  base := (47744425391880908772286346511286949485899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-4430163282634672461555122256452549799000000000000)
      constant := (140612946986450790403756770427985729226991514618691) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree117.table
  base := (47744425388215864618250517394892007884849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-4434731131321483443400418104634838549000000000000)
      constant := (140897377421069041169039883579260069686897400089241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268700630924773543783/50000000000000000000)
  centralHi := (537401261849547087567/100000000000000000000)
  directionLo := (33732042237080254093/6250000000000000000)
  directionHi := (539712675793284065489/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree118.table
  base := (49315948779348958195999067886431385580377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-40212048341800678960381358748544397391000000000000)
      constant := (1287619552627575930422925951644862130928403224969737) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree118.table
  base := (49315948776242442298468872646783687047437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-40253510352957886334054044139737479891000000000000)
      constant := (1290223358932723072138844468736907501052054032777597) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33732042237080254093/6250000000000000000)
  centralHi := (539712675793284065489/100000000000000000000)
  directionLo := (271007116413207698141/50000000000000000000)
  directionHi := (542014232826415396283/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree119.table
  base := (12727424493925426653265710669955925894989/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80081414939314682489336673786571462500000000000)
      linear := (-10138156784972326441691654297253961647750000000000)
      constant := (327478795839949725638598286934418323722693775768509) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree119.table
  base := (50909697973068790017628830566968833651123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-40594440524022421677504325337761412841000000000000)
      constant := (1312563295840333544878128810994269046854344885181763) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271007116413207698141/50000000000000000000)
  centralHi := (542014232826415396283/100000000000000000000)
  directionLo := (544306057986560277281/100000000000000000000)
  directionHi := (272153028993280138641/50000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree120.table
  base := (6565709122556190493616638934227801076723/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4448967496628593471629815210365081250000000000)
      linear := (-567961193583026841293776050409545774875000000000)
      constant := (18505602987145440300483108825162694270512631601707) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree120.table
  base := (52525672978218160700056829088806469386841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-4548374521676328557883845170642816199000000000000)
      constant := (148344023056911683573086353086779582276038120691969) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (544306057986560277281/100000000000000000000)
  centralHi := (272153028993280138641/50000000000000000000)
  directionLo := (13664706842248066517/2500000000000000000)
  directionHi := (546588273689922660681/100000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree121.table
  base := (54163873793202366977609930127900146170489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-41233784736066559379537134069958744991000000000000)
      constant := (1355084247771391727635640652776052265761190472884009) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree121.table
  base := (54163873791311445080381063824478470968209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-41276300866151492364404887733809278741000000000000)
      constant := (1357822093948140973373013348397590313877384562011329) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13664706842248066517/2500000000000000000)
  centralHi := (546588273689922660681/100000000000000000000)
  directionLo := (274430499903796627161/50000000000000000000)
  directionHi := (548860999807593254323/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree122.table
  base := (55824300413653276131232067663374139369921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-41574363534155186185922392510430194191000000000000)
      constant := (1377957681450399536646549542771163617148567606025201) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree122.table
  base := (55824300412050962508431218771375462363191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-41617231037216027707855168931833211691000000000000)
      constant := (1380740955147986384358679483007086683673539807272071) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (274430499903796627161/50000000000000000000)
  centralHi := (548860999807593254323/100000000000000000000)
  directionLo := (275562176869509780347/50000000000000000000)
  directionHi := (110224870747803912139/20000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree123.table
  base := (28753476420782263695863986459569481363453/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17795869986514373886519260841460325000000000000)
      linear := (-2328607907346878499572647275050091299500000000000)
      constant := (77834650895076202653146531185681103937328204094277) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree123.table
  base := (14376738210051715658837886733742761312333/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8897934993257186943259630420730162500000000000)
      linear := (-1165504478007793418091818059162698462250000000000)
      constant := (38995910864211722056149769506475605390169363506197) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (275562176869509780347/50000000000000000000)
  centralHi := (110224870747803912139/20000000000000000000)
  directionLo := (276689225241385685271/50000000000000000000)
  directionHi := (553378450482771370543/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree124.table
  base := (29605915538378007358538333793405114791911/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160162829878629364978673347573142925000000000000)
      linear := (-21127760565166219899346454695686546295500000000000)
      constant := (712141175877107254270975789565654502672130712110391) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree124.table
  base := (5921183107560572005440297653766679756637/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160162829878629364978673347573142925000000000000)
      linear := (-21149545689672549197377865663940538795500000000000)
      constant := (713578800919478860028725117386010796839095572713985) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (276689225241385685271/50000000000000000000)
  centralHi := (553378450482771370543/100000000000000000000)
  directionLo := (555623402704722407353/100000000000000000000)
  directionHi := (277811701352361203677/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree125.table
  base := (60938935119095506237858647269362640905979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-42596099928421066605078167831844541791000000000000)
      constant := (1447733588378859433844740989314186072139110222962699) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree125.table
  base := (60938935118120970765414483197503648457631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-42640021550409633738206012525905010541000000000000)
      constant := (1450655387329927821368620161483621860239683412345711) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (555623402704722407353/100000000000000000000)
  centralHi := (277811701352361203677/50000000000000000000)
  directionLo := (278929660401881252249/50000000000000000000)
  directionHi := (557859320803762504499/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree126.table
  base := (626882649684904744245812762704270163883/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8897934993257186943259630420730162500000000000)
      linear := (-1192685520180824816985095174230999749750000000000)
      constant := (40871595166257176725552158723313244863121012253675) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree126.table
  base := (62688264967664895455638038262420758446909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-4775661302386018786850699302658771499000000000000)
      constant := (163816238620498525993362581623533752432095110811781) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (278929660401881252249/50000000000000000000)
  centralHi := (557859320803762504499/100000000000000000000)
  directionLo := (560086312975148760437/100000000000000000000)
  directionHi := (280043156487574380219/50000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree127.table
  base := (64459820624881248299355307355405197725919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-43277257524598320217848684712787440191000000000000)
      constant := (1495213864573380298490351783562183780612516031601839) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree127.table
  base := (16114955156045475436705703645623708201063/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80081414939314682489336673786571462500000000000)
      linear := (-10830470473134676106276643730488219110250000000000)
      constant := (374557470650651395360269648918024133117415237950903) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (560086312975148760437/100000000000000000000)
  centralHi := (280043156487574380219/50000000000000000000)
  directionLo := (562304485271598533771/100000000000000000000)
  directionHi := (140576121317899633443/25000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree128.table
  base := (33126801044117637998941039650539414611137/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160162829878629364978673347573142925000000000000)
      linear := (-21808918161343473512116971576629444695500000000000)
      constant := (759621452071604167275837294497501794233389630957297) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree128.table
  base := (13250720417528579436236179177026042600353/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-43662812063603239768556856119976809391000000000000)
      constant := (1522306592384269252384997961349371070030968846386965) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (562304485271598533771/100000000000000000000)
  centralHi := (140576121317899633443/25000000000000000000)
  directionLo := (282256970831110942673/50000000000000000000)
  directionHi := (564513941662221885347/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree129.table
  base := (68069609358542319798784636369981044891497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-4884268346752841536735466843747815399000000000000)
      constant := (171496060521637461391944125704252522743115218480273) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree129.table
  base := (68069609358040578011207887634452160225299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-4889304692740863901334126368666749149000000000000)
      constant := (171841808547719328109865002160417758437176438633291) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282256970831110942673/50000000000000000000)
  centralHi := (564513941662221885347/100000000000000000000)
  directionLo := (566714784089386127369/100000000000000000000)
  directionHi := (56671478408938612737/10000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree130.table
  base := (17476960608952608537963298259275584358439/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80081414939314682489336673786571462500000000000)
      linear := (-11074748479716050159251115008550446947750000000000)
      constant := (391969696556992734034526143053414255844392559427959) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree130.table
  base := (34953921217692743415689097454017355066451/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160162829878629364978673347573142925000000000000)
      linear := (-22172336202866155227728709258012337645500000000000)
      constant := (785519468119112579694462261273685930888130376732131) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (566714784089386127369/100000000000000000000)
  centralHi := (56671478408938612737/10000000000000000000)
  directionLo := (568907112523600479383/100000000000000000000)
  directionHi := (71113389065450059923/12500000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree131.table
  base := (71768301320062601115992316282293877066729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-44639572716952827443389718474673236991000000000000)
      constant := (1592485628742921622947022434056943771309024260183449) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree131.table
  base := (71768301319702715593310287611165300155897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-44685602576796845798907699714048608241000000000000)
      constant := (1595694570310535905089841319916818731394246828978857) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (568907112523600479383/100000000000000000000)
  centralHi := (71113389065450059923/12500000000000000000)
  directionLo := (71386378127063054887/12500000000000000000)
  directionHi := (571091025016504439097/100000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree132.table
  base := (73650986011333917685322673940979312408581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-4997794612782383805530552990571631799000000000000)
      constant := (179698341359956382597190097137488223864887618943629) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree132.table
  base := (18412746502757287573522149124854766812489/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8897934993257186943259630420730162500000000000)
      linear := (-1250737020773927253954388358668681699750000000000)
      constant := (45015088309622926382589842898598206031915616454001) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (71386378127063054887/12500000000000000000)
  centralHi := (571091025016504439097/100000000000000000000)
  directionLo := (573266617752039335293/100000000000000000000)
  directionHi := (286633308876019667647/50000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree133.table
  base := (604447172077353970770123153938839371611/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-45320730313130081056160235355616135391000000000000)
      constant := (1642277116718051700328180486222759271366267773261375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree133.table
  base := (590280441479774767343494740809515100449/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40040707469657341244668336893285731250000000000)
      linear := (-5670932864865739560726032763762059267625000000000)
      constant := (205698095343239698027120953170483109335379512428304) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (573266617752039335293/100000000000000000000)
  centralHi := (286633308876019667647/50000000000000000000)
  directionLo := (575433985095878624041/100000000000000000000)
  directionHi := (287716992547939312021/50000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree134.table
  base := (9685379101890156797589077629883133059649/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40040707469657341244668336893285731250000000000)
      linear := (-5707663638902338482818186724510948073875000000000)
      constant := (208432720272285218844607955421353089015454034041969) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree134.table
  base := (1210672387732855133886864897276988982139/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40040707469657341244668336893285731250000000000)
      linear := (-5713549136248806478657317913515050886375000000000)
      constant := (208852415138630079164171254304582764503688803741272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (575433985095878624041/100000000000000000000)
  centralHi := (287716992547939312021/50000000000000000000)
  directionLo := (288796609821594401667/50000000000000000000)
  directionHi := (115518643928637760667/20000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree135.table
  base := (39716197463874389670088488006866571199963/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17795869986514373886519260841460325000000000000)
      linear := (-2555660439405963037162819568697724099500000000000)
      constant := (94046611590018230923965187101648282968662285366867) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree135.table
  base := (4964524682972734561712196837071360979541/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4448967496628593471629815210365081250000000000)
      linear := (-639573934181319266287622562585338056125000000000)
      constant := (23558984086608689239735690942123494653269739812538) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (288796609821594401667/50000000000000000000)
  centralHi := (115518643928637760667/20000000000000000000)
  directionLo := (144936103066197335271/25000000000000000000)
  directionHi := (115948882452957868217/20000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree136.table
  base := (81403982847615468124171302136265485871129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-46342466707395961475316010677030482991000000000000)
      constant := (1718408856044223978040420254678553953233350543579849) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree136.table
  base := (81403982847458814402325496319792940132753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-46390253432119522516159105704168272991000000000000)
      constant := (1721867362126306100115494969498089915955207988441793) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (144936103066197335271/25000000000000000000)
  centralHi := (115948882452957868217/20000000000000000000)
  directionLo := (72735956518972090533/12500000000000000000)
  directionHi := (116377530430355344853/20000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree137.table
  base := (16679559314957729101287645681552125324309/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-46683045505484588281701269117501932191000000000000)
      constant := (1744171304450004185469752834875621250502389227077145) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree137.table
  base := (16679559314931204157737696266304653598801/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-46731183603184057859609386902192205941000000000000)
      constant := (1747680844780517435180745231958983584905203527062405) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72735956518972090533/12500000000000000000)
  centralHi := (116377530430355344853/20000000000000000000)
  directionLo := (584023026858674630731/100000000000000000000)
  directionHi := (146005756714668657683/25000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree138.table
  base := (85413836109338375020045855449542429996443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-5224847144841468343120725284219264599000000000000)
      constant := (196680705981967241333111378319764571379668579847187) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree138.table
  base := (10676729513653262433843416438562311375523/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4448967496628593471629815210365081250000000000)
      linear := (-653779357975674905598050945836335262375000000000)
      constant := (24634545863868005115669452316914634296587287010907) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (584023026858674630731/100000000000000000000)
  centralHi := (146005756714668657683/25000000000000000000)
  directionLo := (117230124469033857763/20000000000000000000)
  directionHi := (36634413896573080551/6250000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree139.table
  base := (21863025362834170262779120025205519437467/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80081414939314682489336673786571462500000000000)
      linear := (-11841050775415460473617946499611207647750000000000)
      constant := (449068501051841087307269172539878100351842783258027) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree139.table
  base := (17490420290248327476434723643327661203911/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-47413043945313128546509949298240071841000000000000)
      constant := (1799886734380280603365662766548068571712117833411955) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117230124469033857763/20000000000000000000)
  centralHi := (36634413896573080551/6250000000000000000)
  directionLo := (588270523016486312591/100000000000000000000)
  directionHi := (36766907688530394537/6250000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree140.table
  base := (89512592600856905981185307115260196205581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-47704781899750468700857044438916279791000000000000)
      constant := (1822614255559019813372820302415978650187062349249661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree140.table
  base := (8951259260077645361771635230132548603031/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160162829878629364978673347573142925000000000000)
      linear := (-23876987058188831944980115248132002395500000000000)
      constant := (913139570662954242060984509314055503037946939815555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (588270523016486312591/100000000000000000000)
  centralHi := (36766907688530394537/6250000000000000000)
  directionLo := (295191405881231336591/50000000000000000000)
  directionHi := (590382811762462673183/100000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree141.table
  base := (45797654778986590205639332824592084864859/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17795869986514373886519260841460325000000000000)
      linear := (-2669186705435505305957905715521540499500000000000)
      constant := (102730394882928337225759815892975112286053182053331) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree141.table
  base := (91595309557905082726738296875010521768367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-5343878254160244359267834632698659749000000000000)
      constant := (205873835892824302894924255761639966441642936300103) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295191405881231336591/50000000000000000000)
  centralHi := (590382811762462673183/100000000000000000000)
  directionLo := (592487569995364979391/100000000000000000000)
  directionHi := (9257618281177577803/1562500000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree142.table
  base := (183008305317890601609343036226624092153/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 128801250000000000000000000000000000000000000
      center := (2266902)
      previous := (1133451)
      next := (1133451)
      square := (7943008821594394216359519320231250000000000)
      linear := (-1199810045028955621742401341992143875000000000)
      constant := (46515387849843131529883251159284863677090385472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree142.table
  base := (93700252322702350659280886397384763638441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1030410000000000000000000000000000000000000000
      center := (18135216)
      previous := (9067608)
      next := (9067608)
      square := (63544070572755153730876154561850000000000000)
      linear := (-9608378190538927708165203906429651000000000000)
      constant := (372871033427663200948635421635825140430068599081) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (592487569995364979391/100000000000000000000)
  centralHi := (9257618281177577803/1562500000000000000)
  directionLo := (594584877686502885951/100000000000000000000)
  directionHi := (9290388713851607593/1562500000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree143.table
  base := (9582742089529180959997907346471597880387/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160162829878629364978673347573142925000000000000)
      linear := (-24363259147008174560006409880165313695500000000000)
      constant := (951395307753174857860667076741599630306848477832735) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree143.table
  base := (47913710447621514090997044608679949452943/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160162829878629364978673347573142925000000000000)
      linear := (-24388382314785634960155537045167901820500000000000)
      constant := (953307105373120866030348356480275402644438307001183) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (594584877686502885951/100000000000000000000)
  centralHi := (9290388713851607593/1562500000000000000)
  directionLo := (149168703350421054221/25000000000000000000)
  directionHi := (119334962680336843377/20000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree144.table
  base := (48988407637821416596287882320897984076917/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17795869986514373886519260841460325000000000000)
      linear := (-2725949838450276440355448788933448699500000000000)
      constant := (107216737265909795982952728826796803628290675197053) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree144.table
  base := (48988407637800774511440105931393768622663/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17795869986514373886519260841460325000000000000)
      linear := (-2728760822257544736875630849353318699500000000000)
      constant := (107432139819312888743210379899158594130339739051167) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149168703350421054221/25000000000000000000)
  centralHi := (119334962680336843377/20000000000000000000)
  directionLo := (299378727167778138721/50000000000000000000)
  directionHi := (598757454335556277443/100000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree145.table
  base := (20029687092777343910659017775124308555499/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-49407675890193602732783336641273525791000000000000)
      constant := (1957204527048591905833241620040797223461642081829095) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree145.table
  base := (25037108865962945513666627676789463815097/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80081414939314682489336673786571462500000000000)
      linear := (-12364656242925085151802909121595917385250000000000)
      constant := (490283949378264840404584521129298354842386877694057) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299378727167778138721/50000000000000000000)
  centralHi := (598757454335556277443/100000000000000000000)
  directionLo := (120166575268975164797/20000000000000000000)
  directionHi := (300416438172437911993/50000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree146.table
  base := (6396392591256025853554640848118245400333/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40040707469657341244668336893285731250000000000)
      linear := (-6218531836035278692396074385218121873875000000000)
      constant := (248087548036629292490821244707387232634149374967546) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree146.table
  base := (51171140730033424274592578708517197084741/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160162829878629364978673347573142925000000000000)
      linear := (-24899777571382437975330958842203801245500000000000)
      constant := (994343026521280903070626275585933659470241147597621) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120166575268975164797/20000000000000000000)
  centralHi := (300416438172437911993/50000000000000000000)
  directionLo := (301450576990374130287/50000000000000000000)
  directionHi := (24116046159229930423/4000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree147.table
  base := (26139588316085998662166462916123696353617/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144286022500000000000000000000000000000000000000
      center := (2539433996)
      previous := (1269716998)
      next := (1269716998)
      square := (8897934993257186943259630420730162500000000000)
      linear := (-1391356485732523787376495931172678449750000000000)
      constant := (55899690069992807500572538381125918912944460167353) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree147.table
  base := (104558353264318976981870404497491560256463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-5571165034869934588234688764714615049000000000000)
      constant := (224047698148464094284498240918228960310689650475367) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (301450576990374130287/50000000000000000000)
  centralHi := (24116046159229930423/4000000000000000000)
  directionLo := (604962360519874827889/100000000000000000000)
  directionHi := (60496236051987482789/10000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree148.table
  base := (106796650876700557776032262584315444766187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-50429412284459483151939111962687873391000000000000)
      constant := (2040269901728749025097023949061172030646273632996347) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree148.table
  base := (106796650876679389080469913355492653293983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-50481415484893946637562480080455468391000000000000)
      constant := (2044365488393941483555357172406888348916337188909423) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (604962360519874827889/100000000000000000000)
  centralHi := (60496236051987482789/10000000000000000000)
  directionLo := (24280662719793793553/4000000000000000000)
  directionHi := (303508283997422419413/50000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree149.table
  base := (109057174297236122905698603395679629950239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-50769991082548109958324370403159322591000000000000)
      constant := (2068343561920094575552844349753463937847250689643759) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree149.table
  base := (109057174297218211832355398493800542378019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-50822345655958481981012761278479401341000000000000)
      constant := (2072494668215892137164551544292943628014041390581939) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24280662719793793553/4000000000000000000)
  centralHi := (303508283997422419413/50000000000000000000)
  directionLo := (152265961805877097589/25000000000000000000)
  directionHi := (609063847223508390357/100000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree150.table
  base := (11133992352601956510278636730145286776833/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17795869986514373886519260841460325000000000000)
      linear := (-2839476104479818709150534935757265099500000000000)
      constant := (116478323505211860952287638624334272852302157433485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree150.table
  base := (111339923526004411021534303063400233335433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-5684808425224779702718115830722592699000000000000)
      constant := (233424091422451625807028242779974250722416614354097) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (152265961805877097589/25000000000000000000)
  centralHi := (609063847223508390357/100000000000000000000)
  directionLo := (611104267837463438261/100000000000000000000)
  directionHi := (305552133918731719131/50000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree151.table
  base := (56822449281559281740507431866028838517247/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160162829878629364978673347573142925000000000000)
      linear := (-25725574339362681785547443642051110495500000000000)
      constant := (1062534342624970472201236484567907805885814122208207) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree151.table
  base := (113644898563105742585763614407472464398257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-51504205998087552667913323674527267241000000000000)
      constant := (2129331952152494163296600062378551642764670490466017) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (611104267837463438261/100000000000000000000)
  centralHi := (305552133918731719131/50000000000000000000)
  directionLo := (76642237288711206899/12500000000000000000)
  directionHi := (613137898309689655193/100000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree152.table
  base := (23194419881719913029938676088326067918557/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-51791727476813990377480145724573670191000000000000)
      constant := (2153720148388511431937522666915328254446601982451585) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree152.table
  base := (28993024852147179672006288152599311305781/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80081414939314682489336673786571462500000000000)
      linear := (-12961284042288022002840901218137800047750000000000)
      constant := (539510014066803819664047360796130672075381518285861) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76642237288711206899/12500000000000000000)
  centralHi := (613137898309689655193/100000000000000000000)
  directionLo := (307582402990680049649/50000000000000000000)
  directionHi := (615164805981360099299/100000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree153.table
  base := (59160763031263880800214187081754777137061/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17795869986514373886519260841460325000000000000)
      linear := (-2896239237494589843548078009169173299500000000000)
      constant := (121253567361642156785667535809727403431392187611949) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree153.table
  base := (23664305212503717180700702080049482274171/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-5798451815579624817201542896730570349000000000000)
      constant := (242993459460695763261084089217171020648048776149695) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307582402990680049649/50000000000000000000)
  centralHi := (615164805981360099299/100000000000000000000)
  directionLo := (61718505708786039587/10000000000000000000)
  directionHi := (617185057087860395871/100000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree154.table
  base := (60346589262483537655365951530838497456117/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160162829878629364978673347573142925000000000000)
      linear := (-26236442536495621995125331302758284295500000000000)
      constant := (1105800438806558159124027360080440540128150164808677) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree154.table
  base := (120693178524959313348627862803265182250053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-52526996511281158698264167268599066091000000000000)
      constant := (2216035188789667162835042799931575298013551892023093) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61718505708786039587/10000000000000000000)
  centralHi := (617185057087860395871/100000000000000000000)
  directionLo := (309599358392021937321/50000000000000000000)
  directionHi := (619198716784043874643/100000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree155.table
  base := (30771764198995038676553384180224903218239/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80081414939314682489336673786571462500000000000)
      linear := (-13203365967769967699158980261497004447750000000000)
      constant := (560207535924804115426842356158163627481905757151759) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree155.table
  base := (61543528397986794467866248028517727845023/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160162829878629364978673347573142925000000000000)
      linear := (-26433963341172847020857224233311499520500000000000)
      constant := (1122661108598731860537176894190691219267385114327663) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (309599358392021937321/50000000000000000000)
  centralHi := (619198716784043874643/100000000000000000000)
  directionLo := (155301462292187476689/25000000000000000000)
  directionHi := (621205849168749906757/100000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree156.table
  base := (627515804378141879644614256438636272413/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72143011250000000000000000000000000000000000000
      center := (1269716998)
      previous := (634858499)
      next := (634858499)
      square := (4448967496628593471629815210365081250000000000)
      linear := (-738250592627340244486405270645270374875000000000)
      constant := (31531277927331821293192299722422238148706982472925) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree156.table
  base := (125503160875622822236410510888317411281703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-5912095205934469931684969962738547999000000000000)
      constant := (252755802263298160224652524364029110690533421158527) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (155301462292187476689/25000000000000000000)
  centralHi := (621205849168749906757/100000000000000000000)
  directionLo := (623206517308611544731/100000000000000000000)
  directionHi := (155801629327152886183/25000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree157.table
  base := (7996343172748240632253573406722725935439/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40040707469657341244668336893285731250000000000)
      linear := (-6686827683407140551175804740866364523875000000000)
      constant := (287483309852396444495537767686371060152691012729918) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree157.table
  base := (3998171586373973521496334187716365479577/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40040707469657341244668336893285731250000000000)
      linear := (-6693723378059345591076876357833858117625000000000)
      constant := (288059399788294695485786338172932624187769372499748) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (623206517308611544731/100000000000000000000)
  centralHi := (155801629327152886183/25000000000000000000)
  directionLo := (312600391630588741399/50000000000000000000)
  directionHi := (625200783261177482799/100000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree158.table
  base := (16300255807633679388567087558202246341181/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40040707469657341244668336893285731250000000000)
      linear := (-6729400033168218901973962045925295673875000000000)
      constant := (291209193481636037847534079277811856841483063993261) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree158.table
  base := (130402046461065462087410258818223655260469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-53890717195539300072065292060694797891000000000000)
      constant := (2334341151007516671620775845455803354191599384580389) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312600391630588741399/50000000000000000000)
  centralHi := (625200783261177482799/100000000000000000000)
  directionLo := (627188708097372320857/100000000000000000000)
  directionHi := (313594354048686160429/50000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree159.table
  base := (132884827966978750689495782173168118556749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-6019531007048264224686328311985979399000000000000)
      constant := (262185913096630144775925536041529964736144701496341) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree159.table
  base := (66442413983487695248220700118090327057617/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17795869986514373886519260841460325000000000000)
      linear := (-3012869298144657523084198514373262824500000000000)
      constant := (131355559915177261399114388654193049467747074103353) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (627188708097372320857/100000000000000000000)
  centralHi := (313594354048686160429/50000000000000000000)
  directionLo := (125834070384663626029/20000000000000000000)
  directionHi := (314585175961659065073/50000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree160.table
  base := (33847458820439049151026849907999790399961/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80081414939314682489336673786571462500000000000)
      linear := (-13629089465380751207140553312086315947750000000000)
      constant := (597466372217237463068779348559234895115518604642441) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree160.table
  base := (1057733088138698084564487443245719023649/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40040707469657341244668336893285731250000000000)
      linear := (-6821572192208546344870731807092832973875000000000)
      constant := (299331497587926121149166197049134663563114104415504) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (125834070384663626029/20000000000000000000)
  centralHi := (314585175961659065073/50000000000000000000)
  directionLo := (315572886950769690003/50000000000000000000)
  directionHi := (631145773901539380007/100000000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree161.table
  base := (27583413681091394547804259563813361402951/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-54856936659611631634947471688816712991000000000000)
      constant := (2420250360850952623115149057004116003561362751943155) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree161.table
  base := (137917068405454569484928717695639247886961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-54913507708732906102416135654766596741000000000000)
      constant := (2425096857698200143654079494230262429472004076289441) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315572886950769690003/50000000000000000000)
  centralHi := (631145773901539380007/100000000000000000000)
  directionLo := (633115032271572390323/100000000000000000000)
  directionHi := (158278758067893097581/25000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree162.table
  base := (140466527338135100945982322610970521426687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-6133057273077806493481414458809795799000000000000)
      constant := (272314203757300852895182629695819464248563077032983) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree162.table
  base := (70233263669066534312695895266532361374903/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17795869986514373886519260841460325000000000000)
      linear := (-3069690993322080080325912047377251649500000000000)
      constant := (136429706080977349750333909100382505297626954077327) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (633115032271572390323/100000000000000000000)
  centralHi := (158278758067893097581/25000000000000000000)
  directionLo := (317539092184999810507/50000000000000000000)
  directionHi := (127015636873999924203/20000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree163.table
  base := (143038212079843448083203769699716421013101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-55538094255788885247717988569759611391000000000000)
      constant := (2481597907763242471714898429422974515665296749250781) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree163.table
  base := (71519106039920864754643789462317619471691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160162829878629364978673347573142925000000000000)
      linear := (-27797684025430988394658349025407231320500000000000)
      constant := (1243282767990806445384654462075467652806859844660571) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (317539092184999810507/50000000000000000000)
  centralHi := (127015636873999924203/20000000000000000000)
  directionLo := (31851764332496414813/5000000000000000000)
  directionHi := (637035286649928296261/100000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree164.table
  base := (145632122630633749922573548812509167351449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-55878673053877512054103247010231060591000000000000)
      constant := (2512560582693583883185401369203272730230938768957769) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree164.table
  base := (36408030657658074178553134666341300304759/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1298574202500000000000000000000000000000000000000
      center := (22854905964)
      previous := (11427452982)
      next := (11427452982)
      square := (80081414939314682489336673786571462500000000000)
      linear := (-13984074555481628033191744812209598897750000000000)
      constant := (629397334317572201778352395510686998472926170151879) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31851764332496414813/5000000000000000000)
  centralHi := (637035286649928296261/100000000000000000000)
  directionLo := (638986394699932084767/100000000000000000000)
  directionHi := (19968324834372877649/3125000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree165.table
  base := (14824825899055663563309792442640150495309/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (5078867992)
      previous := (2539433996)
      next := (2539433996)
      square := (17795869986514373886519260841460325000000000000)
      linear := (-3123291769553674381138250302816806099500000000000)
      constant := (141317547700375456042292150313754831157539081036905) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree165.table
  base := (148248258990555406860746716959049524329099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-6253025376999005275135251160762480949000000000000)
      constant := (283200679258182927411331905492928366083385070287491) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (638986394699932084767/100000000000000000000)
  centralHi := (19968324834372877649/3125000000000000000)
  directionLo := (64093156326247381647/10000000000000000000)
  directionHi := (640931563262473816471/100000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree166.table
  base := (6035464846386466104123816188729853545411/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-56559830650054765666873763891173958991000000000000)
      constant := (2575063735502791184826579104584615803412738868597275) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree166.table
  base := (75443310579830306821295544890313279538131/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160162829878629364978673347573142925000000000000)
      linear := (-28309079282027791409833770822443130745500000000000)
      constant := (1290107932070855624597176547995904049871055212666211) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64093156326247381647/10000000000000000000)
  centralHi := (640931563262473816471/100000000000000000000)
  directionLo := (160717711562956627207/25000000000000000000)
  directionHi := (642870846251826508829/100000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree167.table
  base := (153547209137997291407185949781945374569641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-56900409448143392473259022331645408191000000000000)
      constant := (2606604213381707998825068918582167351244134136914521) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree167.table
  base := (76773604568998206484808368100246160096353/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (45709811928)
      previous := (22854905964)
      next := (22854905964)
      square := (160162829878629364978673347573142925000000000000)
      linear := (-28479544367560059081558911421455097220500000000000)
      constant := (1305909294862254352402750780530883993671323568053393) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (160717711562956627207/25000000000000000000)
  centralHi := (642870846251826508829/100000000000000000000)
  directionLo := (161201074192877325117/25000000000000000000)
  directionHi := (644804296771509300469/100000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree168.table
  base := (156230022925611010760459003452568298503949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-6360109805136891031071586752457428599000000000000)
      constant := (293148588027059255802440858593106585312291000701141) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree168.table
  base := (156230022925610268071089904950317004574371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (10157735984)
      previous := (5078867992)
      next := (5078867992)
      square := (35591739973028747773038521682920650000000000000)
      linear := (-6366668767353850389618678226770458599000000000000)
      constant := (293734921119118151927274393565443673613660118811739) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell202.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161201074192877325117/25000000000000000000)
  centralHi := (644804296771509300469/100000000000000000000)
  directionLo := (161682991782813561221/25000000000000000000)
  directionHi := (129346393426250848977/20000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 12116
  qDenominator := 22791
  table := BinomialMassData.Q12116_22791.Degree169.table
  base := (158935062522549262332507870536433753681441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (91419623856)
      previous := (45709811928)
      next := (45709811928)
      square := (320325659757258729957346695146285850000000000000)
      linear := (-57581567044320646086029539212588306591000000000000)
      constant := (2670262972088291223393194298567273412756383474250321) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q12116_22791.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 24257
  qDenominator := 45582
  table := BinomialMassData.Q24257_45582.Degree169.table
  base := (9933441407659289652243456019982373692411/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 649287101250000000000000000000000000000000000000
      center := (11427452982)
      previous := (5713726491)
      next := (5713726491)
      square := (40040707469657341244668336893285731250000000000)
      linear := (-7205118634656148606252298154869757542625000000000)
      constant := (334450370648049920896753639748837485220218675701782) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q24257_45582.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell202.Kernel169
