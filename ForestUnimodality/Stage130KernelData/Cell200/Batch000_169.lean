import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell200.Parameters
import ForestUnimodality.BinomialMassData.Q12116_22791.Batch000_049
import ForestUnimodality.BinomialMassData.Q12116_22791.Batch050_099
import ForestUnimodality.BinomialMassData.Q12116_22791.Batch100_149
import ForestUnimodality.BinomialMassData.Q12116_22791.Batch150_199
import ForestUnimodality.BinomialMassData.Q24257_45582.Batch000_049
import ForestUnimodality.BinomialMassData.Q24257_45582.Batch050_099
import ForestUnimodality.BinomialMassData.Q24257_45582.Batch100_149
import ForestUnimodality.BinomialMassData.Q24257_45582.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel000
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
  base := (699327786753767789884506097/10000000000000000000000000)
  polynomial :=
    { denominator := 1000000000000000000000000000000000000000
      center := (14)
      previous := (7)
      next := (7)
      square := (72680900877219331568390714000000000000)
      linear := (-5449576169454658884638842400000000000)
      constant := (69932778675376778988450609700000000000000) }

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
  base := (699327786753767789884506097/10000000000000000000000000)
  polynomial :=
    { denominator := 1000000000000000000000000000000000000000
      center := (14)
      previous := (7)
      next := (7)
      square := (72680900877219331568390714000000000000)
      linear := (-5449576169454658884638842400000000000)
      constant := (69932778675376778988450609700000000000000) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel001
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
  base := (194957524133935782814673061603364432524361/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-214851313161345410046581203677904212000000000000)
      constant := (101327595540360044504746371059740497904874858958841) }

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
  base := (4869965163125029638011984113281178734657/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 519429681000000000000000000000000000000000000000
      center := (7272015534)
      previous := (3636007767)
      next := (3636007767)
      square := (37752617157446657563602418256382234000000000000)
      linear := (-43011674392566399653960620554650192400000000000)
      constant := (20249033382406570223787160788128530598474953235336) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel002
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
  base := (116075722554695956157536836053403066985897/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-415549268266265643051103558815602052000000000000)
      constant := (60521611193755824346852868068883814272906110208857) }

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
  base := (115914388618918100570854803768800775717091/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-415963385869238819497547357006295552000000000000)
      constant := (60438265612146897523760934628509680457281124377971) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel003
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
  base := (74239848348747677565783458572186053063143/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (4040008630)
      previous := (2020004315)
      next := (2020004315)
      square := (20973676198581476424223565697990130000000000000)
      linear := (-68471913707909541783958434883699988000000000000)
      constant := (4340563866499471175871105273504301234581937927487) }

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
  base := (37056226187213636608651520880649013689941/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (4040008630)
      previous := (2020004315)
      next := (2020004315)
      square := (20973676198581476424223565697990130000000000000)
      linear := (-68540933308405071191699067915482238000000000000)
      constant := (4333324002665807180453012747312189429595708119738) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel004
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
  base := (254212250169296092548831372929841218711/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 519429681000000000000000000000000000000000000000
      center := (7272015534)
      previous := (3636007767)
      next := (3636007767)
      square := (37752617157446657563602418256382234000000000000)
      linear := (-163389035695221221812029653818199546400000000000)
      constant := (5458544753387937858894929681949511146228238447640) }

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
  base := (20299428122157004740917097429359189819041/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1038859362000000000000000000000000000000000000000
      center := (14544031068)
      previous := (7272015534)
      next := (7272015534)
      square := (75505234314893315127204836512764468000000000000)
      linear := (-327109365472820984781214346188953892800000000000)
      constant := (10898301204781519396251786291829772565322914355921) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel005
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
  base := (73765489834368343792488047536902265876207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-2035286267162052684129341248457391144000000000000)
      constant := (41058568832387280526637051612366318412255387499967) }

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
  base := (73627880957664089621688705534684547723633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-2037356855176918566361560239410858644000000000000)
      constant := (40992674923581188177325635535635094904715965351073) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel006
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
  base := (11179297734375560869142244139523525375431/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 115428818000000000000000000000000000000000000000
      center := (1616003452)
      previous := (808001726)
      next := (808001726)
      square := (8389470479432590569689426279196052000000000000)
      linear := (-54148492830486514447519687971839707200000000000)
      constant := (732567963010278804550595416790887619839503285279) }

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
  base := (55793281109979560730004871328376287483177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-271018542554414689868560971986327536000000000000)
      constant := (3657774657770304683137453587215366117705657997393) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel007
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
  base := (21833080085016160187356525815314848220989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-1419039043790866808073715334504091252000000000000)
      constant := (14007414603445686813746376134335144509991733774509) }

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
  base := (43586166422533879083539811545402848605811/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-2840976910802545851272537256343037004000000000000)
      constant := (27984179692896003188126503206916125360807702476291) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel008
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
  base := (34801867869875720711554126667085142283337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-3239473997791574082156475379283578184000000000000)
      constant := (25025906615769189212040760082267830768073349525497) }

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
  base := (34737903209686185922531150536527433005883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-3242786938615359493728025764809126184000000000000)
      constant := (25006902570832685750844471882283347885994677813323) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel009
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
  base := (28083085971367899026674147648644979053483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-404541100889046060907280009950997096000000000000)
      constant := (2596090359458765637827914517081295720889150736547) }

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
  base := (14015349961174822111333050920314762181741/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (4040008630)
      previous := (2020004315)
      next := (2020004315)
      square := (20973676198581476424223565697990130000000000000)
      linear := (-202477609246009618676861904070845298000000000000)
      constant := (1297532415437562124419622688628834107794732406069) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel010
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
  base := (22818297788455724829742248399137253811393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-4042265818211255014174564799834369544000000000000)
      constant := (22672354773327723493080228580719093862467900155633) }

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
  base := (5560233888019699358653132083614181881/2441406250000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-2023203497120493389319501390870652272000000000000)
      constant := (11335949896679783610126772845938380944480762800128) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel011
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
  base := (18590684248459442786967026299645608425407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-4443661728421095480183609510109765224000000000000)
      constant := (22732023032408926341738437080343839421460070305167) }

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
  base := (463852841749278142780208378849241811133/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 519429681000000000000000000000000000000000000000
      center := (7272015534)
      previous := (3636007767)
      next := (3636007767)
      square := (37752617157446657563602418256382234000000000000)
      linear := (-444821702205380042109449129020739372400000000000)
      constant := (2273984991079759252667855099693822039094705754292) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel012
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
  base := (7566264575913660492522897935219843421851/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (4040008630)
      previous := (2020004315)
      next := (2020004315)
      square := (20973676198581476424223565697990130000000000000)
      linear := (-269169868812829774788480790021397828000000000000)
      constant := (1300264348457822824205640143190345964164668151059) }

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
  base := (3020345041310230496478174316221229413989/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 115428818000000000000000000000000000000000000000
      center := (1616003452)
      previous := (808001726)
      next := (808001726)
      square := (8389470479432590569689426279196052000000000000)
      linear := (-107778378885924756967777328859410731200000000000)
      constant := (520459157967375680637265879611212815281791467501) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel013
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
  base := (6130844431186092610334880444085099831341/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-2623226774420388206100849465330278292000000000000)
      constant := (12297974840991246511126683952588965758246609432221) }

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
  base := (6117863597914974631051198431580495371821/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-2625918538839713853002734153569786042000000000000)
      constant := (12309945433524797592942107763492300815306958419101) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel014
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
  base := (9848320428793896188937665163317995259053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-5647849459050616878210743640935952264000000000000)
      constant := (26238152978860043006993551824577743434969412152093) }

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
  base := (4913233917658770126720476817224899614601/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-2826823552746120674230478407802830632000000000000)
      constant := (13135095595971109032208899663822622390069220372281) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel015
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
  base := (7796618897672281675803116953575967850101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-672138374362273038246643150134594216000000000000)
      constant := (3142400469608911208646099261524227661071579805309) }

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
  base := (1944566692307840389284712620577678674633/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (4040008630)
      previous := (2020004315)
      next := (2020004315)
      square := (20973676198581476424223565697990130000000000000)
      linear := (-336414285183614166162024740226208358000000000000)
      constant := (1573436881473759477373276827800062109096693773794) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel016
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
  base := (6034196500790365176236014183608599016569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-6450641279470297810228833061486743624000000000000)
      constant := (30688703069489720589925111676209881760033349384489) }

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
  base := (300941305871193267460450537663548004897/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 519429681000000000000000000000000000000000000000
      center := (7272015534)
      previous := (3636007767)
      next := (3636007767)
      square := (37752617157446657563602418256382234000000000000)
      linear := (-645726716111786863337193383253783962400000000000)
      constant := (3073735522598393577164191487101630905423670295714) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel017
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
  base := (2252750335088467393876125345362688461129/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-3426018594840069138118938885881069652000000000000)
      constant := (16715296927614292363816742210198387600666617369849) }

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
  base := (1123166118697607111140000855296942945577/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-3429538594465341137913711170501964402000000000000)
      constant := (16743923290878043704264674632873989835492522941874) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel018
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
  base := (1583737520455844781113143223624899628291/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (4040008630)
      previous := (2020004315)
      next := (2020004315)
      square := (20973676198581476424223565697990130000000000000)
      linear := (-402968505549443263458162360113196388000000000000)
      constant := (2026939546100067876612842487874999583731134745019) }

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
  base := (315678557476723651925483997225524267823/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57714409000000000000000000000000000000000000000
      center := (808001726)
      previous := (404000863)
      next := (404000863)
      square := (4194735239716295284844713139598026000000000000)
      linear := (-80676524630483287980921231660777977600000000000)
      constant := (406122271075763249588394060852991815632562161607) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel019
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
  base := (124158913817832454114557244189739893703/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-3827414505049909604127983596156465332000000000000)
      constant := (19917108053505619574216145416837735859672985589944) }

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
  base := (494416242883409606018427695271418173721/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-3831348622278154780369199678968053582000000000000)
      constant := (19954707539486714162634367195742148851287003226002) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel020
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
  base := (187283943872886886218012914217909348639/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1038859362000000000000000000000000000000000000000
      center := (14544031068)
      previous := (7272015534)
      next := (7272015534)
      square := (75505234314893315127204836512764468000000000000)
      linear := (-1611244984061931934853002380517665268800000000000)
      constant := (8692970831490766376018777749188510393450473554159) }

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
  base := (929065535401337388976625585900690746203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-8064507272369123203193887866402196344000000000000)
      constant := (43549450284315947374773953510974436771979876251243) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel021
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
  base := (-1757812664263485848242403599171857821/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (4040008630)
      previous := (2020004315)
      next := (2020004315)
      square := (20973676198581476424223565697990130000000000000)
      linear := (-469867823917750007793003145159095668000000000000)
      constant := (2631450795692493750704121040366682371336428957211) }

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
  base := (-9593386011862311500170256843838535947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-940701922242437427294375152763142836000000000000)
      constant := (5273379979016065977301546798186809074606393639677) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel022
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
  base := (-849465804191610390330875418510860364991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-8859016740729340606283101323139117704000000000000)
      constant := (51529580599152968091396752527633856833577181302129) }

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
  base := (-427238853919631984355495826320256751149/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-4434063663997375244052432441667187352000000000000)
      constant := (25816963301659301393492107780135633445912578546531) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel023
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
  base := (-1614171544221994760089480205462260217963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-9260412650939181072292146033414513384000000000000)
      constant := (55948635075758220874011084104624119589444488440197) }

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
  base := (-809148088133021908605035437512863266731/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-4634968677903782065280176695900231942000000000000)
      constant := (28031684680430549145070775296850739698465298757189) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel024
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
  base := (-2307656591309234816479994059880352507607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-1073534284572113504255687860409989896000000000000)
      constant := (6735341235683423264780041347429291388311793990737) }

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
  base := (-2311044712684315160489466350529721008593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-1074638598180041974779537988918505896000000000000)
      constant := (6749283989501341535115243354382883659054171083463) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel025
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
  base := (-367226190799244762479659687361023529307/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-5031602235679431002155117726982652372000000000000)
      constant := (32766895586124600387604332681381822065354283355732) }

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
  base := (-2940587869579027051218169970013793014887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-10073557411433191415471330408732642244000000000000)
      constant := (65670401155283064520942027691043017653677217338953) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel026
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
  base := (-3510839723095034527269338366732485693603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-10464600381568702470319280164240700424000000000000)
      constant := (70692569896095335633952054855241613927834729969357) }

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
  base := (-1756557206224827659100053926593096767489/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-5237683719623002528963409458599365712000000000000)
      constant := (35420345240842446934716614571292524471261057558991) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel027
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
  base := (-125988604227916712463563709116317923173/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (4040008630)
      previous := (2020004315)
      next := (2020004315)
      square := (20973676198581476424223565697990130000000000000)
      linear := (-603666460654363496462684715250894228000000000000)
      constant := (4227326013359899687750957702743945116927406403888) }

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
  base := (-1008373732399987988421845869405127920813/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (4040008630)
      previous := (2020004315)
      next := (2020004315)
      square := (20973676198581476424223565697990130000000000000)
      linear := (-604287637058823261132350412536934478000000000000)
      constant := (4236216330921592312948453886840944819461757810966) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel028
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
  base := (-2252022340283696439065021024236704832919/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-5633696100994191701168684792395745892000000000000)
      constant := (40864843637512786211372248656311324036145725531161) }

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
  base := (-4505562848712706961011004170543457448263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-11278987494871632342837795934130909784000000000000)
      constant := (81902020383875959631238636079308858493011675905897) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel029
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
  base := (-4931097561481429598449548121200232454789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-11668788112198223868346414295066887464000000000000)
      constant := (87604453230358043554183309383176923134883102807691) }

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
  base := (-4932335412180350883672020191513048110813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-11680797522684445985293284442596998964000000000000)
      constant := (87789502518293387989907220331613416053462750759347) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel030
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
  base := (-5315179416260061252979538216106554230633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-1341131558045340481595051000593587016000000000000)
      constant := (10412769671006616680701795409757708421552566709103) }

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
  base := (-2658093754591338354908119229397749201297/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (4040008630)
      previous := (2020004315)
      next := (2020004315)
      square := (20973676198581476424223565697990130000000000000)
      linear := (-671255975027625534874931830614616008000000000000)
      constant := (5217394820661770915866628302833781468916921611527) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel031
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
  base := (-1414542096528255215013350761818362890439/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-6235789966308952400182251857808839412000000000000)
      constant := (50030066569420323781667482468143255119754064560082) }

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
  base := (-5658988455160381443047496361942000885709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-12484417578310073270204261459529177324000000000000)
      constant := (100271862166808375499315306331862360968434456671171) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel032
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
  base := (-2980771605823683453452268181665678897419/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-6436487921413872633186774212946537252000000000000)
      constant := (53319651713969764864433871920589913145665217106661) }

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
  base := (-5962209632143017421614427087057711158479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-12886227606122886912659749967995266504000000000000)
      constant := (106865004423484645527425919339631685032361112584801) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel033
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
  base := (-6226468174138504969419353881720388165767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-1474930194781953970264732570685385576000000000000)
      constant := (12605759238233857603498465910461779861762163563297) }

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
  base := (-1245401841011230776944514998164392078759/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 115428818000000000000000000000000000000000000000
      center := (1616003452)
      previous := (808001726)
      next := (808001726)
      square := (8389470479432590569689426279196052000000000000)
      linear := (-295289725198571123447005299476919015200000000000)
      constant := (2526487376815618950028159997237660964930142861569) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel034
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
  base := (-6453859968986822559293917655207238384299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-13675767663247426198391637846443865864000000000000)
      constant := (120497246128536816218713643714190277713152615021381) }

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
  base := (-129085975992095938570039796647718323899/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 519429681000000000000000000000000000000000000000
      center := (7272015534)
      previous := (3636007767)
      next := (3636007767)
      square := (37752617157446657563602418256382234000000000000)
      linear := (-1368984766174851419757072698492744486400000000000)
      constant := (12075217124101385445422326085914151831796438768905) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel035
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
  base := (-6644440356250760060300545426581713777947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-14077163573457266664400682556719261544000000000000)
      constant := (127775167477638908860649722819514654531887684955093) }

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
  base := (-1328959196852266600668942078159056988189/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1038859362000000000000000000000000000000000000000
      center := (14544031068)
      previous := (7272015534)
      next := (7272015534)
      square := (75505234314893315127204836512764468000000000000)
      linear := (-2818331537912265568005243098678706808800000000000)
      constant := (25609069910010988657011648652406533794364166962291) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel036
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
  base := (-1699694403512019317379084638534937611961/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (4040008630)
      previous := (2020004315)
      next := (2020004315)
      square := (20973676198581476424223565697990130000000000000)
      linear := (-804364415759283729467207070388592068000000000000)
      constant := (7515850111716087172525780389954712467747599107902) }

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
  base := (-1699766394870499740933539859953684132981/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (4040008630)
      previous := (2020004315)
      next := (2020004315)
      square := (20973676198581476424223565697990130000000000000)
      linear := (-805192650965230082360094666769979068000000000000)
      constant := (7531731861073150769999298854066859873784648353542) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel037
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
  base := (-864664897060692999615062761882709821433/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-7439977696938473798209385988635026452000000000000)
      constant := (71513708658866724495409343606858010856149959388508) }

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
  base := (-6917552173065975964343237329900564884493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-14895277745186955124937192510325712404000000000000)
      constant := (143329412156700461019777712904271643633327999163267) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel038
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
  base := (-3500208665495731631034817747511714080011/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-7640675652043394031213908343772724292000000000000)
      constant := (75500665204812022384447011095798010627656677793509) }

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
  base := (-7000605713856135910600892296329333218953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-15297087772999768767392681018791801584000000000000)
      constant := (151319883748390365491468423105221948507136540056007) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel039
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
  base := (-352417472554123229355065931392233661603/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57714409000000000000000000000000000000000000000
      center := (808001726)
      previous := (404000863)
      next := (404000863)
      square := (4194735239716295284844713139598026000000000000)
      linear := (-174252746825518094760409571086898269600000000000)
      constant := (1768965524561378841320121626676162772461353724746) }

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
  base := (-7048501657299970199524153537558759518813/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-1744321977868064712205352169695321196000000000000)
      constant := (17726938354961245234050745571992423800598583323483) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel040
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
  base := (-3530666963324532301064094849653963665333/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-8042071562253234497222953054048119972000000000000)
      constant := (83822002141121218581232428592096941572930489051227) }

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
  base := (-7061456822655499820142738127067327245969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-16100707828625396052303658035723979944000000000000)
      constant := (167996983873124957365719563593404058503103713794111) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel041
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
  base := (-1759885676674165575388441673144104231997/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-8242769517358154730227475409185817812000000000000)
      constant := (88156281154681023216457507205170742015486096594086) }

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
  base := (-703964187471476000898999109576227734761/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 519429681000000000000000000000000000000000000000
      center := (7272015534)
      previous := (3636007767)
      next := (3636007767)
      square := (37752617157446657563602418256382234000000000000)
      linear := (-1650251785643820969475914654419006912400000000000)
      constant := (17668341113545313147500370848637159809449741158759) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel042
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
  base := (-3491555587452238452517953162040754168481/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (4040008630)
      previous := (2020004315)
      next := (2020004315)
      square := (20973676198581476424223565697990130000000000000)
      linear := (-938163052495897218136888640480390628000000000000)
      constant := (10289583387198978560253637146440988895251832657271) }

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
  base := (-6983191148582451103821535986397571370961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-1878258653805669259690515005850684256000000000000)
      constant := (20622406355999460870696461003785072541289666122951) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel043
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
  base := (-3446072962587497164228505216997137206107/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-8644165427567995196236520119461213492000000000000)
      constant := (97171882447432187656511215519814479019118609738133) }

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
  base := (-6892210383088080262064905422933076163601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-17306137912063836979670123561122247484000000000000)
      constant := (194751667154864526233343085185005656240992028758719) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel044
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
  base := (-3383365441867955626571444969147369266521/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-8844863382672915429241042474598911332000000000000)
      constant := (101853155245718325048870038500130568227901792990199) }

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
  base := (-6766782808014393277102396412029258388611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-17707947939876650622125612069588336664000000000000)
      constant := (204133397756041765319467858493974707128537214236909) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel045
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
  base := (-825866516174410209214195565886539845087/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (4040008630)
      previous := (2020004315)
      next := (2020004315)
      square := (20973676198581476424223565697990130000000000000)
      linear := (-1005062370864203962471729425526289908000000000000)
      constant := (11850005746444680560670119665221504527143408965668) }

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
  base := (-6606973935559283456227524441157320763243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-2012195329743273807175677842006047316000000000000)
      constant := (23749646108727423529462551470883008801126001331613) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel046
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
  base := (-400800105548957774259957223305190851947/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-9246259292882755895250087184874307012000000000000)
      constant := (111562558352195618620394183333195466833032412488744) }

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
  base := (-400802208240996283678089524691558784991/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-9255783997751138953518294543260257512000000000000)
      constant := (111795946018699776210287317599907433357355018257032) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel047
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
  base := (-6184380524546474103672278894217391803067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-18893914495975352256509219080024009704000000000000)
      constant := (233181329019383241048174575563534359559080893368373) }

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
  base := (-6184407585662123477219854641300486217271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-18913378023315091549492077594986604204000000000000)
      constant := (233668607849594492366859861765345683872018027779449) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel048
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
  base := (-2960850444054794791454408357725432024227/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (4040008630)
      previous := (2020004315)
      next := (2020004315)
      square := (20973676198581476424223565697990130000000000000)
      linear := (-1071961689232510706806570210572189188000000000000)
      constant := (13526040201590718629536896206811106410452065013157) }

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
  base := (-5921722645113895213182249353233732568361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-2146132005680878354660840678161410376000000000000)
      constant := (27108549535591278653948997100401025093952992786351) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel049
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
  base := (-5624788172128718301111845185449276738061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-19696706316395033188527308500574801064000000000000)
      constant := (253987287342441089608470751810872486838268254211459) }

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
  base := (-5624805657061381867640968003620510568091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-19716998078940718834403054611918782564000000000000)
      constant := (254516892887560259810826856897600051171559363091029) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel050
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
  base := (-5293662369023538720865231223467642919551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-20098102226604873654536353210850196744000000000000)
      constant := (264737009776151527876651927398736989724475715406769) }

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
  base := (-1058735282973989290203828896226819283603/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1038859362000000000000000000000000000000000000000
      center := (14544031068)
      previous := (7272015534)
      next := (7272015534)
      square := (75505234314893315127204836512764468000000000000)
      linear := (-4023761621350706495371708624076974348800000000000)
      constant := (53057687754009858343552844527300862095873445179357) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel051
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
  base := (-4928339219355354226363781495589506282363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-2277722015201634902282821991236176936000000000000)
      constant := (30635320305961057062045681068641441714311632331533) }

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
  base := (-1232087624507808209032728687397403919691/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (4040008630)
      previous := (2020004315)
      next := (2020004315)
      square := (20973676198581476424223565697990130000000000000)
      linear := (-1140034340809241451073001757158386718000000000000)
      constant := (15349531965296568271518423328019271419781500944762) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel052
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
  base := (-2264415558002007096800250061229195579049/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-10450447023512277293277221315700494052000000000000)
      constant := (143464949918852709910524131639681446296487967646631) }

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
  base := (-141526255287105171301553295929954252227/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-10461214081189579880884760068658525052000000000000)
      constant := (143763148166923392197399006503773178854738173606608) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel053
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
  base := (-2047573908036198783675178080321008240647/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-10651144978617197526281743670838191892000000000000)
      constant := (149186527980095205385048624794834450007962357556393) }

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
  base := (-1023788770051725734466451258945730145347/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-10662119095095986702112504322891569642000000000000)
      constant := (149496298316053975909228147494067756447080648311386) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel054
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
  base := (-3627297001404659751989290683553357710957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-2411520651938248390952503561327975496000000000000)
      constant := (34449705236769625252460963052539255363746523920587) }

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
  base := (-3627302827959054903039526582091672819923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-2414005357556087449631166350472136496000000000000)
      constant := (34521163591564708996224111682193092843376780629493) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel055
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
  base := (-1562642359955069499398599600125281703261/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-11052540888827037992290788381113587572000000000000)
      constant := (160976385104225225521209551481466340324840002110259) }

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
  base := (-3125289391780419839994187596213118170461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-22127858245817600689135985662715317644000000000000)
      constant := (322619920303925169906310737300444766265702139147059) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel056
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
  base := (-1294557866519661720426107905964910650193/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-11253238843931958225295310736251285412000000000000)
      constant := (167044661359761586966324747657823744815776747421567) }

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
  base := (-2589119477818013032097696855039108074967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-22529668273630414331591474171181406824000000000000)
      constant := (334780938127123875751595574008638270354095367104473) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel057
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
  base := (-2018793789368452701639494323210871432569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-2545319288674861879622185131419774056000000000000)
      constant := (38495222524113670621225932331336461924894296813279) }

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
  base := (-1009398395035792744636434676632791276019/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (4040008630)
      previous := (2020004315)
      next := (2020004315)
      square := (20973676198581476424223565697990130000000000000)
      linear := (-1273971016746845998558164593313749778000000000000)
      constant := (19287417992761727189483771090944523279984207542229) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel058
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
  base := (-1414321840005626810572076880174572625513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-23309269508283597382608710893053362184000000000000)
      constant := (359055808668056897022776682862896347828818449948647) }

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
  base := (-1414324243738587761600544212015173504257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-23333288329256041616502451188113585184000000000000)
      constant := (359797676017446729092405889396637163271524134347983) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel059
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
  base := (-96962776023750124420760258108247381451/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-11855332709246718924308877801664378932000000000000)
      constant := (185942869682932692470618652562311113164735287011476) }

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
  base := (-775704133143703980681781220974464114533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-23735098357068855258957939696579674364000000000000)
      constant := (372653393378590456007786302781726674056842176346027) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel060
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
  base := (-51468361412432302806104396850676678321/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (4040008630)
      previous := (2020004315)
      next := (2020004315)
      square := (20973676198581476424223565697990130000000000000)
      linear := (-1339558962705737684145933350755786308000000000000)
      constant := (21385932992247880398872592419360258214260620372711) }

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
  base := (-102938263920470948896381802849531385319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-2681878709431296544601492022782862616000000000000)
      constant := (42860075001693624236965246610936709740169362638529) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel061
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
  base := (603973176385951953241091497569842468649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-24513457238913118780635845023879549224000000000000)
      constant := (398238971404021382376204568343268277372710602570969) }

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
  base := (301985971472697428889969373187193034157/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-12269359206347241271934458356755926362000000000000)
      constant := (199529760094650529026218064793403935505517592613917) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel062
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
  base := (168128294519973316432256013099832316363/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-12457426574561479623322444867077472452000000000000)
      constant := (205881135703941669423731496948913940228967696680812) }

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
  base := (168128171152647058231927453035424262883/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-12470264220253648093162202610988970952000000000000)
      constant := (206304964159961256152864461138566485520275907321292) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel063
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
  base := (1060110962230250181124502574614103652883/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (4040008630)
      previous := (2020004315)
      next := (2020004315)
      square := (20973676198581476424223565697990130000000000000)
      linear := (-1406458281074044428480774135801685588000000000000)
      constant := (23639816300483203866298703103608944019390883491147) }

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
  base := (53005528374152114906042248603336205513/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57714409000000000000000000000000000000000000000
      center := (808001726)
      previous := (404000863)
      next := (404000863)
      square := (4194735239716295284844713139598026000000000000)
      linear := (-281581538536890109208665485893822567600000000000)
      constant := (4737687766111551304649338945654383795417941347268) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel064
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
  base := (117182367167361494015055640145152532579/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1038859362000000000000000000000000000000000000000
      center := (14544031068)
      previous := (7272015534)
      next := (7272015534)
      square := (75505234314893315127204836512764468000000000000)
      linear := (-5143528993908528035732595830941147252800000000000)
      constant := (87900447408354137745518039359024210359669260386495) }

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
  base := (1464779273896398012429055254938138816439/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-12872074248066461735617691119455060132000000000000)
      constant := (220202715860002923479921390073106566448156627325959) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel065
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
  base := (1886518783878391272137484148583815599883/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-13059520439876240322336011932490565972000000000000)
      constant := (226859451010039629853397627495043537618810050327323) }

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
  base := (3773037062930445097919493340746146465499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-26145958523945737113690870747376209444000000000000)
      constant := (454650526346851043965296250753714564645553423075819) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel066
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
  base := (581332081915759583008578238617987247749/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (4040008630)
      previous := (2020004315)
      next := (2020004315)
      square := (20973676198581476424223565697990130000000000000)
      linear := (-1473357599442351172815614920847584868000000000000)
      constant := (26009260450986000246624671796156057051093480461364) }

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
  base := (4650656251789732615020220174283618609039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-2949752061306505639571817695093588736000000000000)
      constant := (52125242511994800607902296840746861962402087942951) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel067
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
  base := (556241609971572626083496584822344118571/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 519429681000000000000000000000000000000000000000
      center := (7272015534)
      previous := (3636007767)
      next := (3636007767)
      square := (37752617157446657563602418256382234000000000000)
      linear := (-2692183270017216157669011328553192330400000000000)
      constant := (48284559515704045191596865783520481467981560705851) }

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
  base := (5562415777220272551844996680870938630047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-26949578579571364398601847764308387804000000000000)
      constant := (483835400328186414015679091008180252387775890225007) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel068
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
  base := (130166312634157879578376482541137590789/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 519429681000000000000000000000000000000000000000
      center := (7272015534)
      previous := (3636007767)
      next := (3636007767)
      square := (37752617157446657563602418256382234000000000000)
      linear := (-2732322861038200204269915799580731898400000000000)
      constant := (49775562299811686675981110612701120356003194041545) }

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
  base := (650831537403556436887802460667651600167/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 519429681000000000000000000000000000000000000000
      center := (7272015534)
      previous := (3636007767)
      next := (3636007767)
      square := (37752617157446657563602418256382234000000000000)
      linear := (-2735138860738417804105733627277447698400000000000)
      constant := (49877517936980493021822449009664194872893884356727) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel069
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
  base := (3744177519759337574277738102884417911739/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (4040008630)
      previous := (2020004315)
      next := (2020004315)
      square := (20973676198581476424223565697990130000000000000)
      linear := (-1540256917810657917150455705893484148000000000000)
      constant := (28494265085053911273734507555196207807085030547251) }

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
  base := (7488354833684235232690582895391928283459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-3083688737244110187056980531248951796000000000000)
      constant := (57105168847164553446197435790843397753250220660731) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel070
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
  base := (68020273252604280706567777176573100541/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1038859362000000000000000000000000000000000000000
      center := (14544031068)
      previous := (7272015534)
      next := (7272015534)
      square := (75505234314893315127204836512764468000000000000)
      linear := (-5625204086160336594943449483271622068800000000000)
      constant := (105653808133815668373053053698616223973179813935525) }

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
  base := (8502533992184899658377861260373731275657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-28155008663009805325968313289706655344000000000000)
      constant := (529349421007037767655974251148469422757294238575417) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel071
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
  base := (2387713212973607371990315692273000624739/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 515205000000000000000000000000000000000000000
      center := (7212870)
      previous := (3606435)
      next := (3606435)
      square := (37445563536447785720692737806370000000000000)
      linear := (-2829539410931513929847876624343732000000000000)
      constant := (53944894896290783894245028548914956514747462598) }

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
  base := (191017054412597502071007088852243709621/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 103041000000000000000000000000000000000000000
      center := (1442574)
      previous := (721287)
      next := (721287)
      square := (7489112707289557144138547561274000000000000)
      linear := (-566491146415842471105411660348596400000000000)
      constant := (10811027245596445421887994990970903120415287305) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel072
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
  base := (5316655511251874941873584834705553281943/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (4040008630)
      previous := (2020004315)
      next := (2020004315)
      square := (20973676198581476424223565697990130000000000000)
      linear := (-1607156236178964661485296490939383428000000000000)
      constant := (31094830027969995403354928710933869792685350616687) }

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
  base := (5316655458855443552949354268453004471947/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (4040008630)
      previous := (2020004315)
      next := (2020004315)
      square := (20973676198581476424223565697990130000000000000)
      linear := (-1608812706590857367271071683702157428000000000000)
      constant := (31158328161238644139630992051912065793372778184323) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel073
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
  base := (5874954293739901619058028725839097218449/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-14665104080715602186372190773592148692000000000000)
      constant := (287886285552106437960626602335791266261506951384769) }

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
  base := (11749908503836310458912618810203835168707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-29360438746448246253334778815104922884000000000000)
      constant := (576947491321031857552637132756489635243658058192467) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel074
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
  base := (806290342703193819159311276905835853483/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-14865802035820522419376713128729846532000000000000)
      constant := (296034661056820820620470089649327813923304299431384) }

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
  base := (3225161354125281291841219900421927830933/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-14881124387130529947895133661785506032000000000000)
      constant := (296638318337129320119096083001070257875253100244746) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel075
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
  base := (14085521659901616117184627218245964632297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-3348111109094542811640274551970565416000000000000)
      constant := (67621910389535371893877383480857851065387923667473) }

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
  base := (14085521606642892497179303763601295554541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-3351562089119319282027306203559677916000000000000)
      constant := (67759704770721272852144413216834938809564661081269) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel076
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
  base := (15304537078260547308904003561889582944093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-30534395892060725770771515678010484424000000000000)
      constant := (625356185260396516685373488170876911009873267824333) }

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
  base := (7652268517886914725092647636490758706661/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-15282934414943343590350622170251595212000000000000)
      constant := (313314805043869303500411407664411929746448895805141) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel077
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
  base := (3311538341522263395910056000131522785509/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1038859362000000000000000000000000000000000000000
      center := (14544031068)
      previous := (7272015534)
      next := (7272015534)
      square := (75505234314893315127204836512764468000000000000)
      linear := (-6187158360454113247356112077657176020800000000000)
      constant := (128469259472284209601025650977869395488121171292629) }

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
  base := (8278845836861873862295095470941367809807/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-15483839428849750411578366424484639802000000000000)
      constant := (321826719056164401473725680183106849437651718681567) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel078
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
  base := (17844985523888094973409863194290201330207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-3481909745831156300309956122062363976000000000000)
      constant := (73285281088487937169264251040781773032263910852663) }

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
  base := (356899709937275964667270173604200138957/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57714409000000000000000000000000000000000000000
      center := (808001726)
      previous := (404000863)
      next := (404000863)
      square := (4194735239716295284844713139598026000000000000)
      linear := (-348549876505692382951246903971504097600000000000)
      constant := (7343431411088761310727910772381663753488105657065) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel079
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
  base := (19166418508256154877024922112043590893333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-31738583622690247168798649808836671464000000000000)
      constant := (677019882555524360307458826324692721091818465216773) }

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
  base := (4791604621677162374629984931994972570699/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-15885649456662564054033854932950728982000000000000)
      constant := (339197888367557961111107737660673635962503863034038) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel080
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
  base := (20521990645994419028136906204104901395551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-32139979532900087634807694519112067144000000000000)
      constant := (694703355631173260683286771110705589342427510749231) }

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
  base := (20521990628816521627866917392286374271161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-32173108941137941750523198374367547144000000000000)
      constant := (696114287316209526595088078479338906768315765729641) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel081
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
  base := (21911701925615912135654585213154954095703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-3615708382567769788979637692154162536000000000000)
      constant := (79179772113041273304417299316735301457055628084527) }

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
  base := (10955850955961825865141353609754503516063/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (4040008630)
      previous := (2020004315)
      next := (2020004315)
      square := (20973676198581476424223565697990130000000000000)
      linear := (-1809717720497264188498815937935202018000000000000)
      constant := (39670242151967699906596376596050770096017998051767) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel082
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
  base := (4667110467635102777853336030698972028249/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1038859362000000000000000000000000000000000000000
      center := (14544031068)
      previous := (7272015534)
      next := (7272015534)
      square := (75505234314893315127204836512764468000000000000)
      linear := (-6588554270663953713365156787932571700800000000000)
      constant := (146152732541894519297514797178037103001261301058569) }

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
  base := (182309002556744289744530752424450569833/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-16488364498381784517717087695649862752000000000000)
      constant := (366122995494094708237730963878035641443671898449472) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel083
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
  base := (24793541876725164377070554153757862447027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-33344167263529609032834828649938254184000000000000)
      constant := (749140496703867642383133172456256122354101114008387) }

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
  base := (3099192733503723313328497721596334442999/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-16689269512288191338944831949882907342000000000000)
      constant := (375329592035493478540480160826369948960485133013276) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel084
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
  base := (26285670535885150634544776166695250709489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-3749507019304383277649319262245961096000000000000)
      constant := (85305383444195801648600035811365960181804988327001) }

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
  base := (26285670528957279902039740076676222079333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-3753372116932132924482794712025767096000000000000)
      constant := (85478215331230660318550088837632989945661455209197) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel085
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
  base := (27811938311506774963981379789369757182987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-34146959083949289964852918070489045544000000000000)
      constant := (786587525589001357128689552008461650404606396037147) }

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
  base := (27811938305987912892233438222869449134091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-34182159080202009962800640916697993044000000000000)
      constant := (788180252716348613176343587100245466233366614354971) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel086
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
  base := (458942893756358734842259925919165537329/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-17274177497079565215430981390382220612000000000000)
      constant := (402828860237965841946303346140373168890911873985568) }

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
  base := (14686172598005573093042943700612751686109/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-17291984554007411802628064712582041112000000000000)
      constant := (403644064137594630788706300121019822974847810001229) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel087
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
  base := (967715350004983559288641259523325717147/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (4040008630)
      previous := (2020004315)
      next := (2020004315)
      square := (20973676198581476424223565697990130000000000000)
      linear := (-1941652828020498383159500416168879828000000000000)
      constant := (45831057536516274433742844238953601863674244337968) }

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
  base := (15483445598329325561250004306922805203783/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (4040008630)
      previous := (2020004315)
      next := (2020004315)
      square := (20973676198581476424223565697990130000000000000)
      linear := (-1943654396434868735983978774090565078000000000000)
      constant := (45923753592020428214956723672787171589458460409247) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel088
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
  base := (6519115261786148542694156117767013654439/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1038859362000000000000000000000000000000000000000
      center := (14544031068)
      previous := (7272015534)
      next := (7272015534)
      square := (75505234314893315127204836512764468000000000000)
      linear := (-7070229362915762272576010440263046516800000000000)
      constant := (168898294226426542126679351265654425701247894003959) }

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
  base := (2037223519133941114951237051478791474693/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-17693794581820225445083553221048130292000000000000)
      constant := (423099280929477769547194105995087935487722436503464) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel089
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
  base := (17129200262675363350642172920064888654111/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-17876271362394325914444548455795314132000000000000)
      constant := (432127513449869678782810409968640728140905396068591) }

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
  base := (34258400523131196037300914290718665977583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-35789399191453264532622594950562349764000000000000)
      constant := (866001119882260267029814832126196638310481490841023) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel090
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
  base := (1123605120262856993856092650131785514067/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (4040008630)
      previous := (2020004315)
      next := (2020004315)
      square := (20973676198581476424223565697990130000000000000)
      linear := (-2008552146388805127494341201214779108000000000000)
      constant := (49124983497754960800943440201786167088946209462448) }

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
  base := (35955363846644475711585782510843687654913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-4021245468807342019453120384336493216000000000000)
      constant := (98448359858419286997921343436435406464383899741417) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel091
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
  base := (9421616569346774666864328186965899995651/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-18277667272604166380453593166070709812000000000000)
      constant := (452237749655652776352460456392427935857237800634662) }

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
  base := (37686466275980621079706099302370371471983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-36593019247078891817533571967494528124000000000000)
      constant := (906300918389130704063210397846326614066543630127423) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel092
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
  base := (4931463476471451747072837256702891537841/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-18478365227709086613458115521208407652000000000000)
      constant := (462466207977312614842192049198019340157113400234884) }

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
  base := (19725853905326101713095699009890886032509/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-18497414637445852729994530237980308652000000000000)
      constant := (463399079436039222666691344313409249480673505499629) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel093
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
  base := (41251088451229218306440574235572522419057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-4150902929514223743658363972521356776000000000000)
      constant := (105068939209930436233348463229551185436055125092313) }

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
  base := (41251088450338388654304401405374299108651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-4155182144744946566938283220491856276000000000000)
      constant := (105280773352716684004365199578068531349845019252259) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel094
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
  base := (21542304097777960660933517424982343747403/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-18879761137918927079467160231483803332000000000000)
      constant := (483269805057722841658727926893916222931345884868443) }

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
  base := (2692788012177942429296418461291703167319/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-18899224665258666372450018746446397832000000000000)
      constant := (484243661148073027416222508115203161831177582361912) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel095
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
  base := (5619033380581149722180912777685402644977/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-19080459093023847312471682586621501172000000000000)
      constant := (493844943816393623340411453940539244296947837449348) }

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
  base := (22476133522042614134079781385239576845861/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-19100129679165073193677763000679442422000000000000)
      constant := (494839622618558905480972717018742694912120565400341) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel096
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
  base := (46854064998484242544068776562503053918771/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-4284701566250837232328045542613155336000000000000)
      constant := (112119031715709525741103912202770226613617002271339) }

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
  base := (46854064998035586618088044108220266164231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-4289118820682551114423446056647219336000000000000)
      constant := (112344747666372940460444633518120371199491289104479) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel097
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
  base := (24395001028547688686001195329501542353951/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-19481855003233687778480727296896896852000000000000)
      constant := (515341901770629483010293675949993279697920757019631) }

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
  base := (3049375128546155990316081326113905727177/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-19501939706977886836133251509145531602000000000000)
      constant := (516378886788441484586320893535301251698752977124296) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel098
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
  base := (50760078220561508071007785969715201842639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-39365105916677216022970499304069189384000000000000)
      constant := (1052527441932447935752371831355825527625972587968159) }

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
  base := (2538003911013882914242017572282778062919/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 519429681000000000000000000000000000000000000000
      center := (7272015534)
      previous := (3636007767)
      next := (3636007767)
      square := (37752617157446657563602418256382234000000000000)
      linear := (-3940568944176858731472199152675715238400000000000)
      constant := (105464437897574080352543522354867517359231628197678) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel099
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
  base := (13191073372248691341046253293506063826209/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (4040008630)
      previous := (2020004315)
      next := (2020004315)
      square := (20973676198581476424223565697990130000000000000)
      linear := (-2209250101493725360498863556352476948000000000000)
      constant := (59700122256389493605056600380440313895291862290962) }

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
  base := (52764293488769025710377679804017802854319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-4423055496620155661908608892802582396000000000000)
      constant := (119640282799332243999423541295469416986215534182471) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel100
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
  base := (27401323931265823668951963860980370794953/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-20083948868548448477494294362309990372000000000000)
      constant := (548454039794509357296994241420356189549284153199993) }

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
  base := (10960529572470427948672872882797675693757/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1038859362000000000000000000000000000000000000000
      center := (14544031068)
      previous := (7272015534)
      next := (7272015534)
      square := (75505234314893315127204836512764468000000000000)
      linear := (-8041861899478842919926593708737866148800000000000)
      constant := (219822454446340725728163005701990693953149652201517) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel101
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
  base := (56875141341326126780849913856696421133189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-40569293647306737420997633434895376424000000000000)
      constant := (1119445078854551402897790388880978848527054020782709) }

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
  base := (28437570670591698537452037724849408655669/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-20305559762603514121044228526077709962000000000000)
      constant := (560846780044481169273407064518669839465552787511589) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel102
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
  base := (117963547851088602278270583516342328311/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57714409000000000000000000000000000000000000000
      center := (808001726)
      previous := (404000863)
      next := (404000863)
      square := (4194735239716295284844713139598026000000000000)
      linear := (-455229883972406420966740868279675245600000000000)
      constant := (12691257760129946952731928468110678753207666659950) }

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
  base := (58981773925430825315970311667925212822339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-4556992172557760209393771728957945456000000000000)
      constant := (127167378751761511582352925533341053686240517382651) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel103
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
  base := (61122545615360252892125495027365736733097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-41372085467726418353015722855446167784000000000000)
      constant := (1165212438260540606744962478845443217493602556852057) }

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
  base := (61122545615270043746336521497346955956281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-41414739580832655526999434069087598284000000000000)
      constant := (1167550818262468647590371802867721769795692089776361) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel104
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
  base := (63297456410952859056187107738302074285357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-41773481377936258819024767565721563464000000000000)
      constant := (1188442798401180459926606665572054131943681289481117) }

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
  base := (63297456410881152830540485897796103454897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-41816549608645469169454922577553687464000000000000)
      constant := (1190826788578901018121243359616709977836620146597857) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel105
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
  base := (65506506312503344330153510251641163465029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-4686097476460677698337090252888551016000000000000)
      constant := (134656030981523213197590051793631514709456540902861) }

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
  base := (65506506312446351135083695454630551991781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-4690928848495364756878934565113308516000000000000)
      constant := (134926035523916150575229725176423451426549413272429) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel106
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
  base := (67749695320193416318528473785953714811297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-42576273198355939751042856986272354824000000000000)
      constant := (1235596879558220367623116548604690884269196975906257) }

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
  base := (4234355957509257585727909753411492210271/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-21310084832135548227182949797242932912000000000000)
      constant := (619036705835798222847280235992360783586120403628408) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel107
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
  base := (7002702343420385583484579380008039525477/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 45369000000000000000000000000000000000000000
      center := (635166)
      previous := (317583)
      next := (317583)
      square := (3297459791898563853926318303466000000000000)
      linear := (-375383606503325881885334105131869600000000000)
      constant := (11001140715999726695618217248807587945231366013) }

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
  base := (70027023434167861193217757200941660238599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 453690000000000000000000000000000000000000000
      center := (6351660)
      previous := (3175830)
      next := (3175830)
      square := (32974597918985638539263183034660000000000000)
      linear := (-3757706323004970748259357856839196000000000000)
      constant := (110231816267625863656105184687985079183364998031) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel108
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
  base := (72338490654713462488907559712461869042169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-4819896113197291187006771822980349576000000000000)
      constant := (142630604653729646430803591395145257874804179913121) }

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
  base := (72338490654684861040853596234657084623377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-4824865524432969304364097401268671576000000000000)
      constant := (142916253116077187318470567882524703724701191139193) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel109
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
  base := (18671024245474569291284545953813161794107/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-21890230464492730574534995558549270932000000000000)
      constant := (654030701742293066985631984085598455896628773379734) }

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
  base := (18671024245468888079685454403719972336077/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-21912799873854768690866182559942066682000000000000)
      constant := (655340026230813304002508324251595360218214601802874) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel110
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
  base := (77063842415931019838939822669481337095899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-44181856839195301615079035827373937544000000000000)
      constant := (1332678485377956373545150099689856663203176283978219) }

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
  base := (7706384241591296567678055934192617570663/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 519429681000000000000000000000000000000000000000
      center := (7272015534)
      previous := (3636007767)
      next := (3636007767)
      square := (37752617157446657563602418256382234000000000000)
      linear := (-4422740977552235102418785362835022254400000000000)
      constant := (133534538769893415667037268467814450271284477048503) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel111
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
  base := (79477726956980694425162983936953332554197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-4953694749933904675676453393072148136000000000000)
      constant := (150836298618196146916496585274416245184945940324573) }

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
  base := (15895545391393270431451421442103456114703/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 115428818000000000000000000000000000000000000000
      center := (1616003452)
      previous := (808001726)
      next := (808001726)
      square := (8389470479432590569689426279196052000000000000)
      linear := (-991760440074114770369852047484806927200000000000)
      constant := (30227606305704561019493498263073147018717519855527) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel112
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
  base := (163851501210424645544809198364764300491/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 519429681000000000000000000000000000000000000000
      center := (7272015534)
      previous := (3636007767)
      next := (3636007767)
      square := (37752617157446657563602418256382234000000000000)
      linear := (-4498464865961498254709712524792472890400000000000)
      constant := (138260601004209869732739620597110351501011413668550) }

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
  base := (1280089853206264533851155158941471106369/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-22515514915573989154549415322641200452000000000000)
      constant := (692685370317512847484800939910337272046462935625248) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel113
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
  base := (3376316534431471124436084500050806843987/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1038859362000000000000000000000000000000000000000
      center := (14544031068)
      previous := (7272015534)
      next := (7272015534)
      square := (75505234314893315127204836512764468000000000000)
      linear := (-9077208913964964602621233991640024916800000000000)
      constant := (281583290562608012222518918066942144700223920890735) }

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
  base := (84407913360777729254425120243477805919677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-45432839858960791951554319153748490084000000000000)
      constant := (1410730758333979147475341063393225950016437735733037) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel114
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
  base := (10865526902982586838036922130030437849101/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (4040008630)
      previous := (2020004315)
      next := (2020004315)
      square := (20973676198581476424223565697990130000000000000)
      linear := (-2543746693335259082173067481581973348000000000000)
      constant := (79636556437592820782758918854411482081888381585236) }

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
  base := (43462107611926753995543281298903591910779/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (4040008630)
      previous := (2020004315)
      next := (2020004315)
      square := (20973676198581476424223565697990130000000000000)
      linear := (-2546369438154089199667211536789698848000000000000)
      constant := (79795685380758168247134531264965074897107790714611) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel115
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
  base := (89474656194586435519614916588118090978053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-46188836390244503945124259378750915944000000000000)
      constant := (1459230699233069978105954931594078954947059047791093) }

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
  base := (22368664048645182045667817016634582029513/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-23118229957293209618232648085340334222000000000000)
      constant := (731072738097054265538104642991630193616816540350706) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel116
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
  base := (92059236273112103709260690453909200418287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-46590232300454344411133304089026311624000000000000)
      constant := (1485234502882314602334683972227022335320235882976447) }

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
  base := (46029618136553785781725150836303805685287/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-23319134971199616439460392339573378812000000000000)
      constant := (744100088177720312674833339553643582478194612803447) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel117
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
  base := (94677955459581586824683223600877513606411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-5221292023407131653015816533255745256000000000000)
      constant := (167941047424942154026755275394131761291183469476099) }

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
  base := (47338977729788994077599328252469876427999/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (4040008630)
      previous := (2020004315)
      next := (2020004315)
      square := (20973676198581476424223565697990130000000000000)
      linear := (-2613337776122891473409792954867380378000000000000)
      constant := (84138135407651004621260237214189391826844993337591) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel118
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
  base := (24332703438533656283994387144835902736357/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-23696512060437012671575696754788551492000000000000)
      constant := (768967735529818457534106883575933569687385887224234) }

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
  base := (1520793964908308873209847990635481658793/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-23720944999012430081915880848039467992000000000000)
      constant := (770502129570506757806358818300426576335862362721056) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel119
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
  base := (100017811156906897357913339089233882396727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-47794420031083865809160438219852498664000000000000)
      constant := (1564632635587857664368464139639493053043723421054087) }

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
  base := (100017811156904628937748455639274285672903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-47843700025837673806287250204545025164000000000000)
      constant := (1567753641765397418692581745713200700579578875633943) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel120
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
  base := (12842368458503764824226590400366682524491/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (4040008630)
      previous := (2020004315)
      next := (2020004315)
      square := (20973676198581476424223565697990130000000000000)
      linear := (-2677545330071872570842749051673771908000000000000)
      constant := (88420051133845002826425005057496874820766504363276) }

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
  base := (102738947668028317783341517717787340101341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-5360612228183387494304748745890123816000000000000)
      constant := (177192731690104247272197646218444147041630895922469) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel121
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
  base := (52747111643816073246449200201135704408217/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-24298605925751773370589263820201645012000000000000)
      constant := (809360162761880243823860389014012278410470450088777) }

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
  base := (105494223287630716998829478307885385492537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-48647320081463301091198227221477203524000000000000)
      constant := (1621947089477702361890288042754944777759950521790697) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel122
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
  base := (1082836380158370925441128642675230566277/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 519429681000000000000000000000000000000000000000
      center := (7272015534)
      previous := (3636007767)
      next := (3636007767)
      square := (37752617157446657563602418256382234000000000000)
      linear := (-4899860776171338720718757235067868570400000000000)
      constant := (164611085093157344187578603508648244489227114676370) }

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
  base := (54141819007917978940355409498831910792501/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-24524565054638057366826857864971646352000000000000)
      constant := (824695577282877152746925874394165915309569251622181) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel123
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
  base := (111107191852765436154917583994748550519127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-5488889296880358630355179673439342376000000000000)
      constant := (185970277403634610460003404686068695504818058000943) }

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
  base := (111107191852764535574374723746819391170997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-5494548904120992041789911582045486876000000000000)
      constant := (186340753386128516112822387390132675324173909795773) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel124
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
  base := (4558595391941365589218694820683332195863/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1038859362000000000000000000000000000000000000000
      center := (14544031068)
      previous := (7272015534)
      next := (7272015534)
      square := (75505234314893315127204836512764468000000000000)
      linear := (-9960279916426613627841132354245895412800000000000)
      constant := (340317052525447079637050631098209168281770738048515) }

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
  base := (113964884798533424988360317856097254896631/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-49852750164901742018564692746875471064000000000000)
      constant := (1704973967205970140694364737954516607511932728304711) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel125
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
  base := (116856716853256763410847217478136844839389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-50202795492342908605214706481504872744000000000000)
      constant := (1729669148915204140518792238596952313789270324504909) }

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
  base := (58428358426628098097775916513138113547839/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-25127280096357277830510090627670780122000000000000)
      constant := (866556357379126892098735453170282523191595790009359) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel126
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
  base := (119782688017043578468525806241260111958407/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-5622687933616972119024861243531140936000000000000)
      constant := (195331572832963888812503306970599300152953292586463) }

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
  base := (119782688017043128358480097132078431419841/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-5628485580058596589275074418200849936000000000000)
      constant := (195720335903562761977214925193885801687043154188969) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel127
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
  base := (122742798290001678635877800599349685114919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-51005587312762589537232795902055664104000000000000)
      constant := (1786530282371703602229710198892796524194692824510839) }

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
  base := (61371399145000660738222462380304639148521/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-25529090124170091472965579136136869302000000000000)
      constant := (895042446163729496202613201041038711982236374651801) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel128
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
  base := (62868523836117544420057894325806647906073/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-25703491611486215001620920306165529892000000000000)
      constant := (907653764770171991452545814962358325285530816352713) }

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
  base := (125737047672234805453966955859658501436607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-51459990276152996588386646780739827784000000000000)
      constant := (1818918322344490224248466748817876950762154815732367) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel129
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
  base := (128765436163844870983273326439269135094131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-5756486570353585607694542813622939496000000000000)
      constant := (204923988555849848432245399899659963147898930033579) }

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
  base := (8047839760240290384115332446413119928723/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (4040008630)
      previous := (2020004315)
      next := (2020004315)
      square := (20973676198581476424223565697990130000000000000)
      linear := (-2881211127998100568380118627178106498000000000000)
      constant := (102665739621289502773854092816613427366758960557656) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel130
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
  base := (131827963764929226528229172172968904590551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-52209775043392110935259930032881851144000000000000)
      constant := (1873555384758668569939597953128500521654389341544231) }

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
  base := (131827963764929048153838687993228890433177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-52263610331778623873297623797672006144000000000000)
      constant := (1877279864843672479832911407480284080937689080926537) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel131
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
  base := (134924630475583595746204320462360624506331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-52611170953601951401268974743157246824000000000000)
      constant := (1903025992808453359562894566729991401198284293810411) }

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
  base := (26984926095116690848311627620188617549299/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1038859362000000000000000000000000000000000000000
      center := (14544031068)
      previous := (7272015534)
      next := (7272015534)
      square := (75505234314893315127204836512764468000000000000)
      linear := (-10533084071918287503150622461227619064800000000000)
      constant := (381361595465184817952667243723006077259263381343619) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel132
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
  base := (34513859073975188388254616328595626469723/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (4040008630)
      previous := (2020004315)
      next := (2020004315)
      square := (20973676198581476424223565697990130000000000000)
      linear := (-2945142603545099548182112191857369028000000000000)
      constant := (107373762286225066378057081411830768539369638677414) }

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
  base := (69027718147950320651865554829483804756157/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (4040008630)
      previous := (2020004315)
      next := (2020004315)
      square := (20973676198581476424223565697990130000000000000)
      linear := (-2948179465966902842122700045255788028000000000000)
      constant := (107587091701667448377415586052488272542572990366213) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel133
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
  base := (7061019061298545095781256300452084253533/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 519429681000000000000000000000000000000000000000
      center := (7272015534)
      previous := (3636007767)
      next := (3636007767)
      square := (37752617157446657563602418256382234000000000000)
      linear := (-5341396277402163233328706416370803818400000000000)
      constant := (196266056978950892924491688823882927570395538625946) }

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
  base := (7061019061298540643920558296879210808011/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 519429681000000000000000000000000000000000000000
      center := (7272015534)
      previous := (3636007767)
      next := (3636007767)
      square := (37752617157446657563602418256382234000000000000)
      linear := (-5346904041521706480066408932307027368400000000000)
      constant := (196655888475598927731834063219995541094773811948982) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel134
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
  base := (144419465265881758850951932840143868762903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-53815358684231472799296108873983433864000000000000)
      constant := (1992824538720872126224113506811215161681620569923943) }

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
  base := (144419465265881688229769911556236951762667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-53870850443029878443119577831536362864000000000000)
      constant := (1996781679703895273327322679697265848050494507519227) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel135
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
  base := (147652688415718644068912224186179165347953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-6024083843826812585033905953806536616000000000000)
      constant := (224802180882909455925813402113521740656170386754777) }

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
  base := (147652688415718588057797247446298055945151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-6030295607871410231730562926666939116000000000000)
      constant := (225248448385975152991600571375636055821723326380759) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel136
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
  base := (3018401013511291226660479340173147150427/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 519429681000000000000000000000000000000000000000
      center := (7272015534)
      previous := (3636007767)
      next := (3636007767)
      square := (37752617157446657563602418256382234000000000000)
      linear := (-5461815050465115373131419829453422522400000000000)
      constant := (205384583746549097518794416188685635407961778118935) }

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
  base := (30184010135112903382378299857086400352117/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1038859362000000000000000000000000000000000000000
      center := (14544031068)
      previous := (7272015534)
      next := (7272015534)
      square := (75505234314893315127204836512764468000000000000)
      linear := (-10934894099731101145606110969693708244800000000000)
      constant := (411584390413135140627240708259802948009138420984677) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel137
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
  base := (154221552045500277627250937042745638124667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-55019546414860994197323243004809620904000000000000)
      constant := (2084703167278831694559699771552370661663237218041227) }

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
  base := (77110776022750121199886313570520193023527/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-27538140263234159685243021678467315202000000000000)
      constant := (1044419714739817602527715494223639855472769055104887) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel138
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
  base := (78778596262802199613970075571156869587903/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (4040008630)
      previous := (2020004315)
      next := (2020004315)
      square := (20973676198581476424223565697990130000000000000)
      linear := (-3078941240281713036851793761949167588000000000000)
      constant := (117543978743680449548924165379330320398555895194327) }

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
  base := (78778596262802185646416246762661905470321/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (4040008630)
      previous := (2020004315)
      next := (2020004315)
      square := (20973676198581476424223565697990130000000000000)
      linear := (-3082116141904507389607862881411151088000000000000)
      constant := (117777137095316428520681999938679312915033443555289) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel139
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
  base := (5028967878623545149569350351119351158493/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-27911169117640337564670666212680206132000000000000)
      constant := (1073555593893889956604647769136787687170927990891728) }

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
  base := (10057935757247088914691627872615799597059/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-27939950291046973327698510186933404382000000000000)
      constant := (1075684533386948487174675646601819239152582279265432) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel140
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
  base := (164330890816621915529836283772383201613087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-56223734145490515595350377135635807944000000000000)
      constant := (2178661878483465856694644794336261343183644465835247) }

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
  base := (164330890816621897965980798733473173541837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-56281710609906760297852508882332897944000000000000)
      constant := (2182981226654277686297557268410553806714894033063997) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel141
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
  base := (167768948627682362694874930038015747960919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-6291681117300039562373269093990133736000000000000)
      constant := (245604854385927067511344198327126650842257395181871) }

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
  base := (1677689486276823487690409132610489062249/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57714409000000000000000000000000000000000000000
      center := (808001726)
      previous := (404000863)
      next := (404000863)
      square := (4194735239716295284844713139598026000000000000)
      linear := (-629816895974661932670088859897766523600000000000)
      constant := (24609166081743061495675619896208283208386652458410) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel142
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
  base := (171241145549205452297601806043802372761073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1030410000000000000000000000000000000000000000
      center := (14425740)
      previous := (7212870)
      next := (7212870)
      square := (74891127072895571441385475612740000000000000)
      linear := (-11312542345945287944330185787777544000000000000)
      constant := (444843606577554031334644205522710928291673722993) }

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
  base := (17124114554920544125679701229811314706381/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 103041000000000000000000000000000000000000000
      center := (1442574)
      previous := (721287)
      next := (721287)
      square := (7489112707289557144138547561274000000000000)
      linear := (-1132420763053608164704691249737454400000000000)
      constant := (44572509995670050097546905537025046478660204621) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel143
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
  base := (2730429399707187927427054889507836296391/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-28713960938060018496688755633230997492000000000000)
      constant := (1137350336167910204434349280184973337917907154600672) }

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
  base := (87373740790630009301147777747239294703967/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-28743570346672600612609487203865582742000000000000)
      constant := (1139603535614434258952286485566348349217246568244527) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel144
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
  base := (17828795672391316766294831712958116088699/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57714409000000000000000000000000000000000000000
      center := (808001726)
      previous := (404000863)
      next := (404000863)
      square := (4194735239716295284844713139598026000000000000)
      linear := (-642547975403665305104295066408193229600000000000)
      constant := (25635287157872111795231415843128394518212654363891) }

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
  base := (178287956723913160723971156506816904784083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-6432105635684223874186051435133028296000000000000)
      constant := (256860608266481583930348908564842334994822622951947) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel145
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
  base := (181862570977230247228863047413087110727413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-58230713696539717925395600687012786344000000000000)
      constant := (2339882136375492787264662564677705088030351812545253) }

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
  base := (181862570977230241728247882403273204397317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-58290760748970828510129951424663343844000000000000)
      constant := (2344515438390158395074286639182014762920946166565877) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel146
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
  base := (46367831085318747367725164698154109541153/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-29316054803374779195702322698644091012000000000000)
      constant := (1186409774418430842892398511427473747247600318324386) }

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
  base := (185471324341274985110700646062765873195969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-58692570776783642152585439933129433024000000000000)
      constant := (2377516963204374036882991039336297310655868628155889) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel147
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
  base := (189114216816109520269059442795644926178989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-6559278390773266539712632234173730856000000000000)
      constant := (267332009065847669684140017473549386080268978352501) }

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
  base := (94557108408054758406500053594042802147939/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (4040008630)
      previous := (2020004315)
      next := (2020004315)
      square := (20973676198581476424223565697990130000000000000)
      linear := (-3283021155810914210835607135644195678000000000000)
      constant := (133930558268945191714295399606828265705172229953051) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel148
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
  base := (192791248401794418968370661729475526571067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-59434901427169239323422734817838973384000000000000)
      constant := (2439387734642826278091916745414005724936116355639627) }

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
  base := (192791248401794416229094154921750707113363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-59496190832409269437496416950061611384000000000000)
      constant := (2444214695300108103732538625329770828029418573927203) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel149
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
  base := (1228140119364929796383147606772633144913/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 519429681000000000000000000000000000000000000000
      center := (7272015534)
      previous := (3636007767)
      next := (3636007767)
      square := (37752617157446657563602418256382234000000000000)
      linear := (-5983629733737907978943177952811436906400000000000)
      constant := (247301850798748412745654780564612184073474981804048) }

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
  base := (98251209549194382625124545917015692703729/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-29949000430111041539975952729263850282000000000000)
      constant := (1238955451290844342198294334393504189343591981980449) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel150
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
  base := (200247728905950197155370317365179189015667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-6693077027509880028382313804265529416000000000000)
      constant := (278542266847403612308567160362311496473138512645803) }

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
  base := (40049545781190039086949221666171537497457/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 115428818000000000000000000000000000000000000000
      center := (1616003452)
      previous := (808001726)
      next := (808001726)
      square := (8389470479432590569689426279196052000000000000)
      linear := (-1339995797511886593831275421488750883200000000000)
      constant := (55818637126350780630920018998566087559287069757913) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel151
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
  base := (40805435564906986949566721243062943735227/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1038859362000000000000000000000000000000000000000
      center := (14544031068)
      previous := (7272015534)
      next := (7272015534)
      square := (75505234314893315127204836512764468000000000000)
      linear := (-12127817831559752144289973789733032084800000000000)
      constant := (508194683112060126761335603796746819924109909072587) }

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
  base := (2040271778245349333842491943336095036959/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 519429681000000000000000000000000000000000000000
      center := (7272015534)
      previous := (3636007767)
      next := (3636007767)
      square := (37752617157446657563602418256382234000000000000)
      linear := (-6070162091584771036486288247545987892400000000000)
      constant := (254599799961242664148274122412921708399232965800790) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel152
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
  base := (207840765854197845485747481705384608881601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-61040485068008601187458913658940556104000000000000)
      constant := (2575297549788516995203820964462893169421679774199281) }

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
  base := (207840765854197844405162364288135692257113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-61103430943660524007318370983925968104000000000000)
      constant := (2580388889361641722339213180848964474361826375570953) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel153
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
  base := (42337698598998495077196577334072767998253/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 115428818000000000000000000000000000000000000000
      center := (1616003452)
      previous := (808001726)
      next := (808001726)
      square := (8389470479432590569689426279196052000000000000)
      linear := (-1365375132849298703410399074871465595200000000000)
      constant := (57996728984695764630199897203404910385613284927477) }

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
  base := (211688492994992474529700243745550978357023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-6833915663497037516641539943599117476000000000000)
      constant := (290556815548162020484360975974251786908247373444407) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel154
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
  base := (107785179623485545823216662255204932516757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-30921638444214141059738501539745673732000000000000)
      constant := (1322319589564352511203064917198916847294805615664517) }

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
  base := (215570359246971090967922547930715772530889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-61907050999286151292229348000858146464000000000000)
      constant := (2649865351327903176683096110757321993743388235916409) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel155
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
  base := (219486364610184721596263100690259716414329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-62244672798638122585486047789766743144000000000000)
      constant := (2679656674240730342454534442380866264624245376299049) }

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
  base := (219486364610184721058639842017214551068707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-62308861027098964934684836509324235644000000000000)
      constant := (2684950923545003204425075812603676903215176686092467) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel156
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
  base := (4468730181693663804197264360187899421661/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 57714409000000000000000000000000000000000000000
      center := (808001726)
      previous := (404000863)
      next := (404000863)
      square := (4194735239716295284844713139598026000000000000)
      linear := (-696067430098310700572167694444912653600000000000)
      constant := (30165614329415680545275143887285816665963032066745) }

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
  base := (223436509084683189783891001556927092473681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-6967852339434642064126702779754480536000000000000)
      constant := (302252006287198238684412685907204713654206846969529) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel157
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
  base := (113710396335257578123059463338613258112167/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-31523732309528901758752068605158767252000000000000)
      constant := (1375192512674386508535210489127142440427573567028727) }

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
  base := (22742079267051515590862446134573773186671/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 519429681000000000000000000000000000000000000000
      center := (7272015534)
      previous := (3636007767)
      next := (3636007767)
      square := (37752617157446657563602418256382234000000000000)
      linear := (-6311248108272459221959581352625641400400000000000)
      constant := (275581675044727128269376621190829405306618870981951) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel158
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
  base := (231439215367728147071669107566770483101243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-63448860529267643983513181920592930184000000000000)
      constant := (2786095881344840333566400531510618177949494542193483) }

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
  base := (23143921536772814680428572083826800241411/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 519429681000000000000000000000000000000000000000
      center := (7272015534)
      previous := (3636007767)
      next := (3636007767)
      square := (37752617157446657563602418256382234000000000000)
      linear := (-6351429111053740586205130203472250318400000000000)
      constant := (279159700513248929515462063312463153069846838719891) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel159
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
  base := (58872944294092148056012400950398588345121/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 288572045000000000000000000000000000000000000000
      center := (4040008630)
      previous := (2020004315)
      next := (2020004315)
      square := (20973676198581476424223565697990130000000000000)
      linear := (-3547236468859860247195679257270462548000000000000)
      constant := (156779880979757628635698490563581338433545893096978) }

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
  base := (47098355435273718402444181807061456078849/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 115428818000000000000000000000000000000000000000
      center := (1616003452)
      previous := (808001726)
      next := (808001726)
      square := (8389470479432590569689426279196052000000000000)
      linear := (-1420357803074449322322373123181968719200000000000)
      constant := (62835751569788051164980618509140438450070227435241) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel160
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
  base := (239578478096481855767957545604242598559743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-64251652349687324915531271341143721544000000000000)
      constant := (2858210954221187526140592367868934356256498365931983) }

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
  base := (9583139123859274224005899552684655900207/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1038859362000000000000000000000000000000000000000
      center := (14544031068)
      previous := (7272015534)
      next := (7272015534)
      square := (75505234314893315127204836512764468000000000000)
      linear := (-12863582233232606629392455810330936308800000000000)
      constant := (572770439394242773589102231082076375347196449219835) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel161
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
  base := (121849659064056133747673935184400613505123/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-32326524129948582690770158025709558612000000000000)
      constant := (1447307585550756995935076547090507018961170331755763) }

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
  base := (9747972725124490694496577545827499012849/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1038859362000000000000000000000000000000000000000
      center := (14544031068)
      previous := (7272015534)
      next := (7272015534)
      square := (75505234314893315127204836512764468000000000000)
      linear := (-12943944238795169357883553512024154144800000000000)
      constant := (580065426824953403585941617221401281696159854855845) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel162
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
  base := (247854297271303153017672244345328478160817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-7228271574456333983061040084632723656000000000000)
      constant := (325694500919626579693310053114209928259920960112153) }

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
  base := (247854297271303152912370953197235682882561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-7235725691309851159097028452065206656000000000000)
      constant := (326337070233460472998471080725940741003278424521449) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel163
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
  base := (252043415526096862796289604603648143064227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-65455840080316846313558405471969908584000000000000)
      constant := (2968116965746585200336138394918237952020093793121587) }

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
  base := (126021707763048431356439945460624149360459/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-32761670624800737037164372288526474542000000000000)
      constant := (1486985845450183791601260566800463995041699572383579) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel164
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
  base := (10250666915701392006196460461712699002749/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1038859362000000000000000000000000000000000000000
      center := (14544031068)
      previous := (7272015534)
      next := (7272015534)
      square := (75505234314893315127204836512764468000000000000)
      linear := (-13171447198105337355913490036449060852800000000000)
      constant := (601042908702274689454884936081230874554434655965345) }

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
  base := (256266672892534800088844719270409564728991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-65925151277414287716784233085519038264000000000000)
      constant := (3011141310522458502694399254764132030002528646581871) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel165
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
  base := (52104813874131489663177849632572242488437/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 115428818000000000000000000000000000000000000000
      center := (1616003452)
      previous := (808001726)
      next := (808001726)
      square := (8389470479432590569689426279196052000000000000)
      linear := (-1472414042238589494346144330944904443200000000000)
      constant := (67612072034911666360931580299784048653024830788733) }

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
  base := (260524069370657448263561304670675085605343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-7369662367247455706582191288220569716000000000000)
      constant := (338726943440826449294404057076592390961736778487287) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel166
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
  base := (264815604960504396500197934974764457365441/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-66660027810946367711585539602796095624000000000000)
      constant := (3080103059925560381055049839526578950483469119054321) }

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
  base := (264815604960504396458753314818669417973129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-66728771333039915001695210102451216624000000000000)
      constant := (3086175232235326769885043873358334154266238063041849) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel167
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
  base := (134570639831057182564560363780115925878843/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2597148405000000000000000000000000000000000000000
      center := (36360077670)
      previous := (18180038835)
      next := (18180038835)
      square := (188763085787233287818012091281911170000000000000)
      linear := (-33530711860578104088797292156535745652000000000000)
      constant := (1558946999287499872124943076814761433826267064139083) }

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
  base := (269141279662114365096297075357095921005967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-67130581360852728644150698610917305804000000000000)
      constant := (3124039534326144793937004739021181462667530637906527) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel168
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
  base := (273501093475525230163878413017836825476557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 577144090000000000000000000000000000000000000000
      center := (8080017260)
      previous := (4040008630)
      next := (4040008630)
      square := (41947352397162952848447131395980260000000000000)
      linear := (-7495868847929560960400403224816320776000000000000)
      constant := (350657339724373638858320504179143872568815630609813) }

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
  base := (54700218695105046027576679618720195903249/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 115428818000000000000000000000000000000000000000
      center := (1616003452)
      previous := (808001726)
      next := (808001726)
      square := (8389470479432590569689426279196052000000000000)
      linear := (-1500719808637012050813470824875186555200000000000)
      constant := (70269675494220261993427060828350005308520237214841) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell200.Kernel169
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
  base := (277895046400774046617781553954653961384439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-67864215541575889109612673733622282664000000000000)
      constant := (3194169236758668644953788347763818185803305468133959) }

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
  base := (277895046400774046597195274919085259518191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5194296810000000000000000000000000000000000000000
      center := (72720155340)
      previous := (36360077670)
      next := (36360077670)
      square := (377526171574466575636024182563822340000000000000)
      linear := (-67934201416478355929061675627849484164000000000000)
      constant := (3200462820976647004660619675235056602664336164827071) }

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
end ForestUnimodality.Stage130KernelData.Cell200.Kernel169
