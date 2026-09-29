import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell143.Parameters
import ForestUnimodality.BinomialMassData.Q111_211.Batch000_049
import ForestUnimodality.BinomialMassData.Q111_211.Batch050_099
import ForestUnimodality.BinomialMassData.Q23557_44732.Batch000_049
import ForestUnimodality.BinomialMassData.Q23557_44732.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree000.table
  base := (2430505922398232747441149117/62500000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (78)
      previous := (39)
      next := (39)
      square := (1180025828053616054891250500000000000000)
      linear := (-60873411699563801519063944000000000000)
      constant := (388880947583717239590583858720000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree000.table
  base := (2430505922398232747441149117/62500000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (78)
      previous := (39)
      next := (39)
      square := (1180025828053616054891250500000000000000)
      linear := (-60873411699563801519063944000000000000)
      constant := (388880947583717239590583858720000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree001.table
  base := (108481852373345665313486818086232041004651/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-57984914999963763250646201771824000000000000)
      constant := (9675405913430308818051186350077197395136134342) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree001.table
  base := (216781874792604258717591267044826149433071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-163044579095337255825338291456322366000000000000)
      constant := (27155566726597823172934635201253724214187498960719) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49929059361808908931/100000000000000000000)
  directionHi := (12482264840452227233/25000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree002.table
  base := (3173642630324854731134488718187703505543/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-113259684837651246493862157692824000000000000)
      constant := (5712757567048339680633559271804237910811196120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree002.table
  base := (126756078014762297724146966316577919469939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-318476360429840441109805022317680116000000000000)
      constant := (16023777123645799663065848272280320394593722201171) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49929059361808908931/100000000000000000000)
  centralHi := (12482264840452227233/25000000000000000000)
  directionLo := (35305176453000754351/50000000000000000000)
  directionHi := (70610352906001508703/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree003.table
  base := (78494360174081998270402915255189498553121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-168534454675338729737078113613824000000000000)
      constant := (3629776441883588527093578056668063665083500041) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree003.table
  base := (19585571433124878959751853122582777716781/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-473908141764343626394271753179037866000000000000)
      constant := (10177817837506596107761542283443969220094874339636) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35305176453000754351/50000000000000000000)
  centralHi := (70610352906001508703/100000000000000000000)
  directionLo := (21619916897193883463/25000000000000000000)
  directionHi := (86479667588775533853/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree004.table
  base := (51342326373956306775959922064054010495081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-223809224513026212980294069534824000000000000)
      constant := (2524140148835748323751065235311444601251501201) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree004.table
  base := (1600933625513757437596540970945320733271/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-629339923098846811678738484040395616000000000000)
      constant := (7077652868420296495102715616658975415007249872608) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21619916897193883463/25000000000000000000)
  centralHi := (86479667588775533853/100000000000000000000)
  directionLo := (49929059361808908931/50000000000000000000)
  directionHi := (99858118723617817863/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree005.table
  base := (17637578805245465311482175298450695296641/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-279083994350713696223510025455824000000000000)
      constant := (1941091328539959226549763271349266810603507922) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree005.table
  base := (137473532402860898685916545473274252699/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-784771704433349996963205214901753366000000000000)
      constant := (5444470832775260443550339168234780433294815567616) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49929059361808908931/50000000000000000000)
  centralHi := (99858118723617817863/100000000000000000000)
  directionLo := (4465790831425079499/4000000000000000000)
  directionHi := (27911192696406746869/25000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree006.table
  base := (6279191651125951152180879147676455307409/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-334358764188401179466725981376824000000000000)
      constant := (1650185399239756510600591168707357866964624356) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree006.table
  base := (25055831005026848363389315803167423439913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-940203485767853182247671945763111116000000000000)
      constant := (4630901340345311522145414889471424977842141984457) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4465790831425079499/4000000000000000000)
  centralHi := (27911192696406746869/25000000000000000000)
  directionLo := (122300718773563334747/100000000000000000000)
  directionHi := (30575179693390833687/25000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree007.table
  base := (182237995846303730354114904216367208791/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-389633534026088662709941937297824000000000000)
      constant := (1533737607680218791680640714603156450258411100) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree007.table
  base := (18176684197212931459718930373389884731699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-1095635267102356367532138676624468866000000000000)
      constant := (4306660786356785803015292114746157350565179041811) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122300718773563334747/100000000000000000000)
  centralHi := (30575179693390833687/25000000000000000000)
  directionLo := (33024968566681922891/25000000000000000000)
  directionHi := (26419974853345538313/20000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree008.table
  base := (3306991838026420940030870361199589980019/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-444908303863776145953157893218824000000000000)
      constant := (1530830350443131635435647724735259782001703596) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree008.table
  base := (6594954653250362355421533642221920878383/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-1251067048436859552816605407485826616000000000000)
      constant := (4300933595648935373110296840262782227298018252574) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33024968566681922891/25000000000000000000)
  centralHi := (26419974853345538313/20000000000000000000)
  directionLo := (35305176453000754351/25000000000000000000)
  directionHi := (28244141162400603481/20000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree009.table
  base := (9406039975661792711433050308436129692853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-500183073701463629196373849139824000000000000)
      constant := (1609264707758514903861635692724200930055508413) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree009.table
  base := (9374083289414079680235220938644799553583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-1406498829771362738101072138347184366000000000000)
      constant := (4523498971051808325270275341019237084928518099087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35305176453000754351/25000000000000000000)
  centralHi := (28244141162400603481/20000000000000000000)
  directionLo := (74893589042713363397/50000000000000000000)
  directionHi := (29957435617085345359/20000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree010.table
  base := (397724498920749775430915870473288567151/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-555457843539151112439589805060824000000000000)
      constant := (1751480463162226391216646594883700484770074736) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree010.table
  base := (253438712083387258613396981539272172583/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-1561930611105865923385538869208542116000000000000)
      constant := (4925178726226026914489930847717335568378744752175) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74893589042713363397/50000000000000000000)
  centralHi := (29957435617085345359/20000000000000000000)
  directionLo := (31577909802613838313/20000000000000000000)
  directionHi := (78944774506534595783/50000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree011.table
  base := (3875830022760594772816869874995182809279/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-610732613376838595682805760981824000000000000)
      constant := (1947469591894175774519864613331824533851910359) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree011.table
  base := (481436697705574198621542084427629970533/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-1717362392440369108670005600069899866000000000000)
      constant := (5477950873656720330449942827594798375017536301096) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31577909802613838313/20000000000000000000)
  centralHi := (78944774506534595783/50000000000000000000)
  directionLo := (10349747252406361673/6250000000000000000)
  directionHi := (165595956038501786769/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree012.table
  base := (1807155169187105635383643055872300094229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-666007383214526078926021716902824000000000000)
      constant := (2191195094144963826910825159191578672495169309) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree012.table
  base := (1785481356540584762844711496483708903799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-1872794173774872293954472330931257616000000000000)
      constant := (6164909962720049231936358206981228024333853098711) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10349747252406361673/6250000000000000000)
  centralHi := (165595956038501786769/100000000000000000000)
  directionLo := (21619916897193883463/12500000000000000000)
  directionHi := (34591867035510213541/20000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree013.table
  base := (14048041962338687716436471941389228143/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-721282153052213562169237672823824000000000000)
      constant := (2478769075100241669600282759432524949130772515) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree013.table
  base := (50837687155975703531596871608796150339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-2028225955109375479238939061792615366000000000000)
      constant := (6975164132362299351887729070342232368716562516771) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21619916897193883463/12500000000000000000)
  centralHi := (34591867035510213541/20000000000000000000)
  directionLo := (180021783664687346863/100000000000000000000)
  directionHi := (11251361479042959179/6250000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree014.table
  base := (-13950180042217597966659816820309408007/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-776556922889901045412453628744824000000000000)
      constant := (2807515682469786074041684874846236484612035300) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree014.table
  base := (-282482895697829722395293119361222642257/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-2183657736443878664523405792653973116000000000000)
      constant := (7901212683111136079263069308306894598720548866635) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180021783664687346863/100000000000000000000)
  centralHi := (11251361479042959179/6250000000000000000)
  directionLo := (186817433775786915807/100000000000000000000)
  directionHi := (5838044805493341119/3125000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree015.table
  base := (-2632512943941163574024984635600232314883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-831831692727588528655669584665824000000000000)
      constant := (3175480735029963481222400525887302057109093957) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree015.table
  base := (-1324051081599852972545262809216633533827/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-2339089517778381849807872523515330866000000000000)
      constant := (8937574629890185052133289125230005036168662331194) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186817433775786915807/100000000000000000000)
  centralHi := (5838044805493341119/3125000000000000000)
  directionLo := (96687207700043711349/50000000000000000000)
  directionHi := (193374415400087422699/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree016.table
  base := (-1837923570190654316819779427411411580437/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-887106462565276011898885540586824000000000000)
      constant := (3581168214496573972600446083431217090054728646) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree016.table
  base := (-3689793046014023983853196200109856069167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-2494521299112885035092339254376688616000000000000)
      constant := (10080052015911996998417227928251751112126426324337) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96687207700043711349/50000000000000000000)
  centralHi := (193374415400087422699/100000000000000000000)
  directionLo := (7988649497889425429/4000000000000000000)
  directionHi := (99858118723617817863/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree017.table
  base := (-455163735391076562641567392898712304161/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-942381232402963495142101496507824000000000000)
      constant := (4023393116081248414226836875393272295064481190) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree017.table
  base := (-2282042456957483744575748704525029773779/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-2649953080447388220376805985238046366000000000000)
      constant := (11325318535527963999362247801033581905812825322138) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7988649497889425429/4000000000000000000)
  centralHi := (99858118723617817863/50000000000000000000)
  directionLo := (205862785536472432847/100000000000000000000)
  directionHi := (12866424096029527053/6250000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree018.table
  base := (-2640728994418696887025665679687499317277/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-997656002240650978385317452428824000000000000)
      constant := (4501194925729796605692356176934897685791021366) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree018.table
  base := (-5292540624567344792888580997598387157169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-2805384861781891405661272716099404116000000000000)
      constant := (12670677548777145391697598187937838487900282173359) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205862785536472432847/100000000000000000000)
  centralHi := (12866424096029527053/6250000000000000000)
  directionLo := (211831058718004526107/100000000000000000000)
  directionHi := (52957764679501131527/25000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree019.table
  base := (-2941528767124209841088359694316728859277/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-1052930772078338461628533408349824000000000000)
      constant := (5013783462959566131287742377305205828912257366) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree019.table
  base := (-294645010879869575192100384873232618921/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-2960816643116394590945739446960761866000000000000)
      constant := (14113910495369044399195953429190425488242160172620) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211831058718004526107/100000000000000000000)
  centralHi := (52957764679501131527/25000000000000000000)
  directionLo := (217635724104168429593/100000000000000000000)
  directionHi := (108817862052084214797/50000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree020.table
  base := (-6371172795582845753569408341814767479797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-1108205541916025944871749364270824000000000000)
      constant := (5560502630455607165038935268062544737031957763) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree020.table
  base := (-797486634415154213037993948103091799671/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-3116248424450897776230206177822119616000000000000)
      constant := (15653175326277920657546282286125740381704434975048) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217635724104168429593/100000000000000000000)
  centralHi := (108817862052084214797/50000000000000000000)
  directionLo := (4465790831425079499/2000000000000000000)
  directionHi := (223289541571253974951/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree021.table
  base := (-6758109459786912238566733702573398197111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-1163480311753713428114965320191824000000000000)
      constant := (6140804566729386144760666336139133738866421169) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree021.table
  base := (-1353163521626522276647937661077701790089/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-3271680205785400961514672908683477366000000000000)
      constant := (17286934008584420754929721747747161066435421977395) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4465790831425079499/2000000000000000000)
  centralHi := (223289541571253974951/100000000000000000000)
  directionLo := (22880369390343285037/10000000000000000000)
  directionHi := (228803693903432850371/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree022.table
  base := (-3527089214518756878988632951917148514383/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-1218755081591400911358181276112824000000000000)
      constant := (6754230220105085545039917217290721261982308914) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree022.table
  base := (-7060977305867205675266229073359295620133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-3427111987119904146799139639544835116000000000000)
      constant := (19013897993114777714684128180899150853346228907963) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22880369390343285037/10000000000000000000)
  centralHi := (228803693903432850371/100000000000000000000)
  directionLo := (58547011725947013077/25000000000000000000)
  directionHi := (234188046903788052309/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree023.table
  base := (-7268036976807933571404562000379930704943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-1274029851429088394601397232033824000000000000)
      constant := (7400394160110401321875877947881337105085232697) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree023.table
  base := (-909252736075930059088640073629089426807/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-3582543768454407332083606370406192866000000000000)
      constant := (20832985550295490566953877693597103230235709427016) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58547011725947013077/25000000000000000000)
  centralHi := (234188046903788052309/100000000000000000000)
  directionLo := (239451356816715220311/100000000000000000000)
  directionHi := (29931419602089402539/12500000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree024.table
  base := (-7406962898923323758236887413008900148487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-1329304621266775877844613187954824000000000000)
      constant := (8078972371997401879542103563111606756489210273) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree024.table
  base := (-7412221562814255109484785602437298527777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-3737975549788910517368073101267550616000000000000)
      constant := (22743287471821629740179382088014475475575756074047) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239451356816715220311/100000000000000000000)
  centralHi := (29931419602089402539/12500000000000000000)
  directionLo := (122300718773563334747/50000000000000000000)
  directionHi := (48920287509425333899/20000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree025.table
  base := (-3738539406619351364468405249837805499771/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-1384579391104463361087829143875824000000000000)
      constant := (8789692270696563943386390057117042122689390618) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree025.table
  base := (-3740845726904276095395933470919814168637/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-3893407331123413702652539832128908366000000000000)
      constant := (24744039003245392193535730348554733916440593907014) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122300718773563334747/50000000000000000000)
  centralHi := (48920287509425333899/20000000000000000000)
  directionLo := (15602831050565284041/6250000000000000000)
  directionHi := (249645296809044544657/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree026.table
  base := (-233860555201509060396734935500733776639/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-1439854160942150844331045099796824000000000000)
      constant := (9532324437416014169311296607911322608968162592) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree026.table
  base := (-7487577335411983799426571036691984285451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-4048839112457916887937006562990266116000000000000)
      constant := (26834596616722132540412643208012061935865467805461) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15602831050565284041/6250000000000000000)
  centralHi := (249645296809044544657/100000000000000000000)
  directionLo := (50917849596239228517/20000000000000000000)
  directionHi := (127294623990598071293/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree027.table
  base := (-7430677900766487504726676481864798830821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-1495128930779838327574261055717824000000000000)
      constant := (10306675733726225159854975557680845291253018259) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree027.table
  base := (-7434210394976679494021272233017029006977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-4204270893792420073221473293851623866000000000000)
      constant := (29014418656174830195145760391816156162339278945247) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50917849596239228517/20000000000000000000)
  centralHi := (127294623990598071293/50000000000000000000)
  directionLo := (259439002766326601557/100000000000000000000)
  directionHi := (129719501383163300779/50000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree028.table
  base := (-7322151886937209300188666372775647252533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-1550403700617525810817477011638824000000000000)
      constant := (11112583539073007126271920659957527408669978307) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree028.table
  base := (-732523673716189937046593521581898679341/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-4359702675126923258505940024712981616000000000000)
      constant := (31283049141617957571024991916232342343118396832510) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259439002766326601557/100000000000000000000)
  centralHi := (129719501383163300779/50000000000000000000)
  directionLo := (33024968566681922891/12500000000000000000)
  directionHi := (264199748533455383129/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree029.table
  base := (-3580517758936870865779809338751444757159/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-1605678470455213294060692967559824000000000000)
      constant := (11949910916080067644192193041429689855933048322) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree029.table
  base := (-716372602283731993464868934771653823043/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-4515134456461426443790406755574339366000000000000)
      constant := (33640104182831749628628662832005632582303459949730) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33024968566681922891/12500000000000000000)
  centralHi := (264199748533455383129/100000000000000000000)
  directionLo := (67219053332135718999/25000000000000000000)
  directionHi := (268876213328542875997/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree030.table
  base := (-6949918957848578865276340067507828795871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-1660953240292900777303908923480824000000000000)
      constant := (12818542548043831005283959632277203954179027209) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree030.table
  base := (-1390452548416703761116713769458916145637/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-4670566237795929629074873486435697116000000000000)
      constant := (36085260564807403762098041335931285306663936002535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67219053332135718999/25000000000000000000)
  centralHi := (268876213328542875997/100000000000000000000)
  directionLo := (68368180218693081529/25000000000000000000)
  directionHi := (273472720874772326117/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree031.table
  base := (-334549174380080703686303256939005086099/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-1716228010130588260547124879401824000000000000)
      constant := (13718381322164476416715168361052015091235728420) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree031.table
  base := (-6693022966110878100456596993018917028163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-4825998019130432814359340217297054866000000000000)
      constant := (38618246149191321972363105238862262521374536611293) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68368180218693081529/25000000000000000000)
  centralHi := (273472720874772326117/100000000000000000000)
  directionLo := (277993237384304320823/100000000000000000000)
  directionHi := (34749154673038040103/12500000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree032.table
  base := (-3193033042977131771676953828035623551747/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-1771502779968275743790340835322824000000000000)
      constant := (14649345454307895608449096317833620007705343626) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree032.table
  base := (-6387838922825657462754212065713404209333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-4981429800464935999643806948158412616000000000000)
      constant := (41238831798497815888508118390968694161130365989163) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277993237384304320823/100000000000000000000)
  centralHi := (34749154673038040103/12500000000000000000)
  directionLo := (282441411624006034809/100000000000000000000)
  directionHi := (28244141162400603481/10000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree033.table
  base := (-1509178448339445884113108203531867880557/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-1826777549805963227033556791243824000000000000)
      constant := (15611366068686158200432216207586722840358887212) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree033.table
  base := (-3019126672513556969090301339766285055107/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-5136861581799439184928273679019770366000000000000)
      constant := (43946824579351346884817665319004796807409963479354) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282441411624006034809/100000000000000000000)
  centralHi := (28244141162400603481/10000000000000000000)
  directionLo := (286820609386627322133/100000000000000000000)
  directionHi := (143410304693313661067/50000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree034.table
  base := (-2822114741443753204966155881910605601063/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-1882052319643650710276772747164824000000000000)
      constant := (16604385160087077320802508040003331856070148354) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree034.table
  base := (-5645565219659196893882753090934967935293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-5292293363133942370212740409881128116000000000000)
      constant := (46742062041108486981794470783966818846780872354723) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286820609386627322133/100000000000000000000)
  centralHi := (143410304693313661067/50000000000000000000)
  directionLo := (72783485823395786547/25000000000000000000)
  directionHi := (291133943293583146189/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree035.table
  base := (-5209710401209550732293917929506460279757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-1937327089481338193519988703085824000000000000)
      constant := (17628353877991830704771766689857782881884938603) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree035.table
  base := (-5210868302951434212440529368183671766459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-5447725144468445555497207140742485866000000000000)
      constant := (49624407399174080855731844733669341116992910120549) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72783485823395786547/25000000000000000000)
  centralHi := (291133943293583146189/100000000000000000000)
  directionLo := (14769214933978915187/5000000000000000000)
  directionHi := (295384298679578303741/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree036.table
  base := (-1183520155947028590054920644013268888883/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-1992601859319025676763204659006824000000000000)
      constant := (18683231081636676799562633634806805023192159828) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree036.table
  base := (-4735083547499885911834841394320021594477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-5603156925802948740781673871603843616000000000000)
      constant := (52593745479687072017367763766384163872925741157747) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14769214933978915187/5000000000000000000)
  centralHi := (295384298679578303741/100000000000000000000)
  directionLo := (74893589042713363397/25000000000000000000)
  directionHi := (299574356170853453589/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree037.table
  base := (-263632399150024492490589373614605244493/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-2047876629156713160006420614927824000000000000)
      constant := (19768982123186579125005577758331054558558834352) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree037.table
  base := (-263686650293753565354532878391421045693/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-5758588707137451926066140602465201366000000000000)
      constant := (55649979305092194267801239254377000270918604305968) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74893589042713363397/25000000000000000000)
  centralHi := (299574356170853453589/100000000000000000000)
  directionLo := (151853305729523386411/50000000000000000000)
  directionHi := (303706611459046772823/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree038.table
  base := (-1831239551193132650392951724399306544471/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-2103151398994400643249636570848824000000000000)
      constant := (20885577822984232794151075325350148946667213218) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree038.table
  base := (-183161490647431820355603666663869402169/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-5914020488471955111350607333326559116000000000000)
      constant := (58793027219247209227267843744078920489040187367180) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151853305729523386411/50000000000000000000)
  centralHi := (303706611459046772823/100000000000000000000)
  directionLo := (307783392685004104969/100000000000000000000)
  directionHi := (30778339268500410497/10000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree039.table
  base := (-3067714746912876707497827048793744068273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-2158426168832088126492852526769824000000000000)
      constant := (22032993606543221474256494271995689720336417767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree039.table
  base := (-306836355360155530694857298775618496327/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-6069452269806458296635074064187916866000000000000)
      constant := (62022820466776682398920443126846380332153970030970) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307783392685004104969/100000000000000000000)
  centralHi := (30778339268500410497/10000000000000000000)
  directionLo := (77951718944102860401/25000000000000000000)
  directionHi := (62361375155282288321/20000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree040.table
  base := (-2434290181812976259417049926825634398443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-2213700938669775609736068482690824000000000000)
      constant := (23211208777749889295473769242304755930946919197) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree040.table
  base := (-2434850548733743439745103472955870046727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-6224884051140961481919540795049274616000000000000)
      constant := (65339301154882476255446052732798062212405915257497) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (77951718944102860401/25000000000000000000)
  centralHi := (62361375155282288321/20000000000000000000)
  directionLo := (31577909802613838313/10000000000000000000)
  directionHi := (315779098026138383131/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree041.table
  base := (-110162306496007980058378552416917941481/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-2268975708507463092979284438611824000000000000)
      constant := (24420205906772996831229311464465426341237190384) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree041.table
  base := (-881540291977885239007485620284367546099/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-6380315832475464667204007525910632366000000000000)
      constant := (68742420537175313400601261111384924932243350233178) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31577909802613838313/10000000000000000000)
  centralHi := (315779098026138383131/100000000000000000000)
  directionLo := (319701970151822104703/100000000000000000000)
  directionHi := (2497671641811110193/781250000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree042.table
  base := (-526482311842039853907298883416553826613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-2324250478345150576222500394532824000000000000)
      constant := (25659970314575747826058093983506631214170725254) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree042.table
  base := (-105338186314525163180583615478225622469/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-6535747613809967852488474256771990116000000000000)
      constant := (72232137568645971457678880254345873327273199416590) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319701970151822104703/100000000000000000000)
  centralHi := (2497671641811110193/781250000000000000)
  directionLo := (323577287039296980693/100000000000000000000)
  directionHi := (161788643519648490347/50000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree043.table
  base := (-152835508097810385089899766614534334517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-2379525248182838059465716350453824000000000000)
      constant := (26930489638783288280262694112189840633785937286) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree043.table
  base := (-61206147529591661306302039967823641799/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-6691179395144471037772940987633347866000000000000)
      constant := (75808417688936363792407047001389441188822490096445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323577287039296980693/100000000000000000000)
  centralHi := (161788643519648490347/50000000000000000000)
  directionLo := (327406737341287202251/100000000000000000000)
  directionHi := (81851684335321800563/25000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree044.table
  base := (239525033207087127768514778359577242887/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-2434800018020525542708932306374824000000000000)
      constant := (28231753468065602945269424531449349476861144254) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree044.table
  base := (14960628175876316291233569813207721137/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-6846611176478974223057407718494705616000000000000)
      constant := (79471231797840432552704534877432511661799927007776) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327406737341287202251/100000000000000000000)
  centralHi := (81851684335321800563/25000000000000000000)
  directionLo := (10349747252406361673/3125000000000000000)
  directionHi := (331191912077003573537/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree045.table
  base := (650500839438850961133760270971357741583/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-2490074787858213025952148262295824000000000000)
      constant := (29563753034222432848011354386769411636026033486) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree045.table
  base := (325183681593818023160646337807460638091/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-7002042957813477408341874449356063366000000000000)
      constant := (83220555392664163960150763838536448257399097581996) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10349747252406361673/3125000000000000000)
  centralHi := (331191912077003573537/100000000000000000000)
  directionLo := (13397372494275238497/4000000000000000000)
  directionHi := (167467156178440481213/50000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree046.table
  base := (27000224476422827570916485362911664679/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-2545349557695900509195364218216824000000000000)
      constant := (30926480952863542731548915793296879217853900720) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree046.table
  base := (2159788162827111040339887032469279441381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-7157474739147980593626341180217421116000000000000)
      constant := (87056367841872606041367575780665300556137313314309) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13397372494275238497/4000000000000000000)
  centralHi := (167467156178440481213/50000000000000000000)
  directionLo := (338635356338837928513/100000000000000000000)
  directionHi := (169317678169418964257/50000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree047.table
  base := (381994902227201828305428299378685449963/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-2600624327533587992438580174137824000000000000)
      constant := (32319931005014950696970703808051535639342421784) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree047.table
  base := (3055761501302550237251489893875722313917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-7312906520482483778910807911078778866000000000000)
      constant := (90978651773492034691931814516176357370334357608413) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338635356338837928513/100000000000000000000)
  centralHi := (169317678169418964257/50000000000000000000)
  directionLo := (85574096376870516689/25000000000000000000)
  directionHi := (342296385507482066757/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree048.table
  base := (997176954305965308848661238126091065561/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-2655899097371275475681796130058824000000000000)
      constant := (33744097953192149010213133260078798801319365124) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree048.table
  base := (3988537778384470420829785631486187500423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-7468338301816986964195274641940136616000000000000)
      constant := (94987392560137273283017219312403851287361087663847) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85574096376870516689/25000000000000000000)
  centralHi := (342296385507482066757/100000000000000000000)
  directionLo := (345918670355102135409/100000000000000000000)
  directionHi := (34591867035510213541/10000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree049.table
  base := (2479082340931931659287308776988949036119/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-2711173867208962958925012085979824000000000000)
      constant := (35198977386500716557748331265719926000074107998) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree049.table
  base := (2479009254832231699417013985087984099791/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-7623770083151490149479741372801494366000000000000)
      constant := (99082577885398531818798748675202033063369974933598) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (345918670355102135409/100000000000000000000)
  centralHi := (34591867035510213541/10000000000000000000)
  directionLo := (349503415532662362519/100000000000000000000)
  directionHi := (8737585388316559063/2500000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree050.table
  base := (5964246373417634792737863183914444286329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-2766448637046650442168228041900824000000000000)
      constant := (36684565590183209239164125764682254974071653409) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree050.table
  base := (5964120770272473265648385210511816846081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-7779201864485993334764208103662852116000000000000)
      constant := (103264197378733935716318654461929779168232481512609) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349503415532662362519/100000000000000000000)
  centralHi := (8737585388316559063/2500000000000000000)
  directionLo := (353051764530007543511/100000000000000000000)
  directionHi := (44131470566250942939/12500000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree051.table
  base := (3503441311001581607383192324258434062169/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-2821723406884337925411443997821824000000000000)
      constant := (38200859435754209978480460403900743485763652098) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree051.table
  base := (350338736832393222921792010323510380301/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-7934633645820496520048674834524209866000000000000)
      constant := (107532242308044671731573311918021149079182774523780) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353051764530007543511/100000000000000000000)
  centralHi := (44131470566250942939/12500000000000000000)
  directionLo := (4457060049210320869/1250000000000000000)
  directionHi := (356564803936825669521/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree052.table
  base := (8086014247920789594671558058952956497703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-2876998176722025408654659953742824000000000000)
      constant := (39747856288474310257804051659220692576234235263) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree052.table
  base := (4042960808340677666021094414530609485251/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-8090065427154999705333141565385567616000000000000)
      constant := (111886705320819595869862656948902973126168086193478) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4457060049210320869/1250000000000000000)
  centralHi := (356564803936825669521/100000000000000000000)
  directionLo := (180021783664687346863/50000000000000000000)
  directionHi := (360043567329374693727/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree053.table
  base := (9201591411388819535141288622042838973687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-2932272946559712891897875909663824000000000000)
      constant := (41325553929426589260872167758354941233947518927) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree053.table
  base := (9201511906869927478391835683966607940383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-2935385264681204304242651582857574000000000000)
      constant := (41412452910706983602390588152791405602113791543) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180021783664687346863/50000000000000000000)
  centralHi := (360043567329374693727/100000000000000000000)
  directionLo := (363489038822379080249/100000000000000000000)
  directionHi := (1453956155289516321/400000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree054.table
  base := (10353572138506717693058301414750799360907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-2987547716397400375141091865584824000000000000)
      constant := (42933950489891021253673884504455016338346940547) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree054.table
  base := (5176751962410311225047541906211050705521/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-8400928989824006075902075027108283116000000000000)
      constant := (120854861811334871258702038549357490643771091477538) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363489038822379080249/100000000000000000000)
  centralHi := (1453956155289516321/400000000000000000)
  directionLo := (183451078160345002121/50000000000000000000)
  directionHi := (366902156320690004243/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree055.table
  base := (1154192107985158375034163993199025413649/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-3042822486235087858384307821505824000000000000)
      constant := (44573044396075949291147919632957958104410671290) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree055.table
  base := (11541862573601433302505696620501745684269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-8556360771158509261186541757969640866000000000000)
      constant := (125468545687092076572381376599192789775132636478541) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (183451078160345002121/50000000000000000000)
  centralHi := (366902156320690004243/100000000000000000000)
  directionLo := (92570953625289194261/25000000000000000000)
  directionHi := (74056762900231355409/20000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree056.table
  base := (6383304232496832934751188539197161939529/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-3098097256072775341627523777426824000000000000)
      constant := (46242834322572070391737428620650937693419541218) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree056.table
  base := (2553311660262050000536618980011076243361/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-8711792552493012446471008488830998616000000000000)
      constant := (130168628157701756021411854267561672142673831512645) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92570953625289194261/25000000000000000000)
  centralHi := (74056762900231355409/20000000000000000000)
  directionLo := (186817433775786915807/50000000000000000000)
  directionHi := (74726973510314766323/20000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree057.table
  base := (7013804611005456860038785774599975572331/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-3153372025910462824870739733347824000000000000)
      constant := (47943319153152342952679870857704599024911496902) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree057.table
  base := (14027566225019758504206603376218673413293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-8867224333827515631755475219692356366000000000000)
      constant := (134955106111317734887005579625554669517574308387277) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186817433775786915807/50000000000000000000)
  centralHi := (74726973510314766323/20000000000000000000)
  directionLo := (75391226338092460449/20000000000000000000)
  directionHi := (188478065845231151123/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree058.table
  base := (15324902235962370934697593817807672622341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-3208646795748150308113955689268824000000000000)
      constant := (49674497947758480655543583067965207392819243661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree058.table
  base := (3064973078625773678029656610336376944931/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-9022656115162018817039941950553714116000000000000)
      constant := (139827976927743487069778747672345053747222260001295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75391226338092460449/20000000000000000000)
  centralHi := (188478065845231151123/50000000000000000000)
  directionLo := (190124193744373440433/50000000000000000000)
  directionHi := (380248387488746880867/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree059.table
  base := (16658469724389874740813135170444228616867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-3263921565585837791357171645189824000000000000)
      constant := (51436369914697663635531897478186863502251535707) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree059.table
  base := (8329219082127048169345730782873934024837/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-9178087896496522002324408681415071866000000000000)
      constant := (144787238400756608892464942810823615931381657056586) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (190124193744373440433/50000000000000000000)
  centralHi := (380248387488746880867/100000000000000000000)
  directionLo := (76702476402407564847/20000000000000000000)
  directionHi := (95878095503009456059/25000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree060.table
  base := (281692136115290788823199620742458722413/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-3319196335423525274600387601110824000000000000)
      constant := (53228934387227188429445681375910240305955147072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree060.table
  base := (1802826968424898482852210160658542712537/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-9333519677831025187608875412276429616000000000000)
      constant := (149832888672705134846288424926245813011145511135930) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76702476402407564847/20000000000000000000)
  centralHi := (95878095503009456059/25000000000000000000)
  directionLo := (96687207700043711349/25000000000000000000)
  directionHi := (386748830800174845397/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree061.table
  base := (971718529231096048614423477077771651803/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-3374471105261212757843603557031824000000000000)
      constant := (55052190803834550352349790211507953434198427260) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree061.table
  base := (19434347445848495114199697291749687569489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-9488951459165528372893342143137787366000000000000)
      constant := (154964926179436890398179203273051594925599946331121) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96687207700043711349/25000000000000000000)
  centralHi := (386748830800174845397/100000000000000000000)
  directionLo := (194979209849446069729/50000000000000000000)
  directionHi := (389958419698892139459/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree062.table
  base := (20876680722390600650459571995070881533809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-3429745875098900241086819512952824000000000000)
      constant := (56906138691629743443811780841964838716766710489) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree062.table
  base := (20876660917884609041737423920277599636761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-9644383240500031558177808873999145116000000000000)
      constant := (160183349603929384624656962241405944865719916275129) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (194979209849446069729/50000000000000000000)
  centralHi := (389958419698892139459/100000000000000000000)
  directionLo := (393141806556886476911/100000000000000000000)
  directionHi := (24571362909805404807/6250000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree063.table
  base := (11177609089687156656886708378444859946947/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-3485020644936587724330035468873824000000000000)
      constant := (58790777652358606225629941697550699219396054774) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree063.table
  base := (11177600616540855589659916727767566785153/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-9799815021834534743462275604860502866000000000000)
      constant := (165488157837245660237658347557541357790099213933634) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393141806556886476911/100000000000000000000)
  centralHi := (24571362909805404807/6250000000000000000)
  directionLo := (99074905700045768673/25000000000000000000)
  directionHi := (396299622800183074693/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree064.table
  base := (23869975422103902085893222913044688984641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-3540295414774275207573251424794824000000000000)
      constant := (60706107350623558364512882955194798598285201961) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree064.table
  base := (2386996092517683568495051709445441197243/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-9955246803169037928746742335721860616000000000000)
      constant := (170879349945658685989358833596711063319067577888270) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99074905700045768673/25000000000000000000)
  centralHi := (396299622800183074693/100000000000000000000)
  directionLo := (7988649497889425429/2000000000000000000)
  directionHi := (399432474894471271451/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree065.table
  base := (25420946106129705168316538672560858714787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-3595570184611962690816467380715824000000000000)
      constant := (62652127503963356467529476958711141990841032027) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree065.table
  base := (25420933707572027479599219475328171196073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-10110678584503541114031209066583218366000000000000)
      constant := (176356925142969734069129942007840440893335408186697) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7988649497889425429/2000000000000000000)
  centralHi := (399432474894471271451/100000000000000000000)
  directionLo := (201270472852501057321/50000000000000000000)
  directionHi := (402540945705002114643/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree066.table
  base := (27008124888365916890115630939997441721417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-3650844954449650174059683336636824000000000000)
      constant := (64628837874498477380404350102957610102879206257) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree066.table
  base := (2700811428695722820600911353768851285821/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-10266110365838044299315675797444576116000000000000)
      constant := (181920882767200153460252954556986003040217672054690) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201270472852501057321/50000000000000000000)
  centralHi := (402540945705002114643/100000000000000000000)
  directionLo := (50703199470335526207/12500000000000000000)
  directionHi := (405625595762684209657/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree067.table
  base := (14315753634525531714951901575336177468631/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-3706119724287337657302899292557824000000000000)
      constant := (66636238261895040527135545270177991914161841502) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree067.table
  base := (14315749103189374975163324920219887347107/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-10421542147172547484600142528305933866000000000000)
      constant := (187571222260965593455555870330208090636783534096646) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (50703199470335526207/12500000000000000000)
  centralHi := (405625595762684209657/100000000000000000000)
  directionLo := (408686964444166650633/100000000000000000000)
  directionHi := (204343482222083325317/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree068.table
  base := (7572772364662638684665255489733001703631/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-3761394494125025140546115248478824000000000000)
      constant := (68674328497439176424150641555790443875389423004) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree068.table
  base := (15145540856550636860283819490714958028999/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-10576973928507050669884609259167291616000000000000)
      constant := (193307943154950892709649151504794353979526124243022) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408686964444166650633/100000000000000000000)
  centralHi := (204343482222083325317/50000000000000000000)
  directionLo := (82345114214588973139/20000000000000000000)
  directionHi := (12866424096029527053/3125000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree069.table
  base := (999589633305154152635846372542334384483/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-3816669263962712623789331204399824000000000000)
      constant := (70743108439046589804857277062290388612210164576) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree069.table
  base := (31986861647346280198882026093295637044893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-10732405709841553855169075990028649366000000000000)
      constant := (199131045053995764243465841640410376005013788639677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82345114214588973139/20000000000000000000)
  centralHi := (12866424096029527053/3125000000000000000)
  directionLo := (207370957973927494113/50000000000000000000)
  directionHi := (414741915947854988227/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree070.table
  base := (1348753640109147131197705473538259360441/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-3871944033800400107032547160320824000000000000)
      constant := (72842577967059724071721763210404601124654844025) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree070.table
  base := (16859417674304337186414711803599618548081/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-10887837491176057040453542720890007116000000000000)
      constant := (205040527625378800392853697224735361557435863581218) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (207370957973927494113/50000000000000000000)
  centralHi := (414741915947854988227/100000000000000000000)
  directionLo := (208868240652362374461/50000000000000000000)
  directionHi := (417736481304724748923/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree071.table
  base := (17743502703053816028480569559482743320079/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-3927218803638087590275763116241824000000000000)
      constant := (74972736980708227037760210681948066430706474318) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree071.table
  base := (1774350028838722413900519384350821528877/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-11043269272510560225738009451751364866000000000000)
      constant := (211036390588952488020042993619739407734881127277060) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (208868240652362374461/50000000000000000000)
  centralHi := (417736481304724748923/100000000000000000000)
  directionLo := (420709732216415083399/100000000000000000000)
  directionHi := (2103548661082075417/500000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree072.table
  base := (1864567978487185929486283832910176446707/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-3982493573475775073518979072162824000000000000)
      constant := (77133585395128035018041857584066407311676846940) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree072.table
  base := (1491654217828039357798623062526168460257/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-11198701053845063411022476182612722616000000000000)
      constant := (217118633708836795140650927937440857471191430716825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (420709732216415083399/100000000000000000000)
  centralHi := (2103548661082075417/500000000000000000)
  directionLo := (211831058718004526107/50000000000000000000)
  directionHi := (84732423487201810443/20000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree073.table
  base := (39131901888366738235794314491161814679917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-4037768343313462556762195028083824000000000000)
      constant := (79325123138850913454285546530182467151364584757) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree073.table
  base := (19565949183645519022376762275577382285053/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-11354132835179566596306942913474080366000000000000)
      constant := (223287256786425092021651421568430381141302761035834) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211831058718004526107/50000000000000000000)
  centralHi := (84732423487201810443/20000000000000000000)
  directionLo := (426594070187476660413/100000000000000000000)
  directionHi := (213297035093738330207/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree074.table
  base := (20504315505052760748647836805542920589307/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-4093043113151150040005410984004824000000000000)
      constant := (81547350151690206009276545855536528735113073894) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree074.table
  base := (5126078500550315267660391969740704645201/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-11509564616514069781591409644335438116000000000000)
      constant := (229542259654495072362834112902867837992430106898312) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (426594070187476660413/100000000000000000000)
  centralHi := (213297035093738330207/50000000000000000000)
  directionLo := (214753004453879993371/50000000000000000000)
  directionHi := (429506008907759986743/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree075.table
  base := (21460772898246967375879811224363158761909/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-4148317882988837523248626939925824000000000000)
      constant := (83800266382960261948008862832534044382477901178) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree075.table
  base := (42921543231198119157882434426894000289687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-11664996397848572966875876375196795866000000000000)
      constant := (235883642172250096593459430832015841639644108189943) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (214753004453879993371/50000000000000000000)
  centralHi := (429506008907759986743/100000000000000000000)
  directionLo := (216199168971938834631/50000000000000000000)
  directionHi := (432398337943877669263/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree076.table
  base := (44870645288788888487162048184026184212733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-4203592652826525006491842895846824000000000000)
      constant := (86083871789976880182317671934313253747335085893) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree076.table
  base := (22435321549879661038203655483625316495397/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-11820428179183076152160343106058153616000000000000)
      constant := (242311404221143960612195359282087791812755239344266) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216199168971938834631/50000000000000000000)
  centralHi := (432398337943877669263/100000000000000000000)
  directionLo := (435271448208336859187/100000000000000000000)
  directionHi := (108817862052084214797/25000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree077.table
  base := (2928495542475261072804456630718389122687/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-4258867422664212489735058851767824000000000000)
      constant := (88398166336794419455417553706050562434098366832) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree077.table
  base := (1171398170299379568778313497335084211303/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-11975859960517579337444809836919511366000000000000)
      constant := (248825545701365317078632004019445755267750848166680) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435271448208336859187/100000000000000000000)
  centralHi := (108817862052084214797/25000000000000000000)
  directionLo := (438125717795860409403/100000000000000000000)
  directionHi := (109531429448965102351/25000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree078.table
  base := (48877395289021196387418180161997620307541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-4314142192501899972978274807688824000000000000)
      constant := (90743149993142223580928781181803368053712032861) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree078.table
  base := (12219348423968105473834526645922872109377/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-12131291741852082522729276567780869116000000000000)
      constant := (255426066528877531063517875529432314250644158913412) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438125717795860409403/100000000000000000000)
  centralHi := (109531429448965102351/25000000000000000000)
  directionLo := (440961512564183941943/100000000000000000000)
  directionHi := (55120189070522992743/12500000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree079.table
  base := (25467522272234993804129231885113420281311/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-4369416962339587456221490763609824000000000000)
      constant := (93118822733528905434400659738406265168688494062) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree079.table
  base := (50935043185685210944206770117528159454729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-12286723523186585708013743298642226866000000000000)
      constant := (262112966632926217152875326284128989784768927373481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (440961512564183941943/100000000000000000000)
  centralHi := (55120189070522992743/12500000000000000000)
  directionLo := (221889593340724290907/50000000000000000000)
  directionHi := (88755837336289716363/20000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree080.table
  base := (10605775192757113804706943604734729165927/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-4424691732177274939464706719530824000000000000)
      constant := (95525184536487997860943652338925894385981179835) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree080.table
  base := (53028874805073795473289317229489136892229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-12442155304521088893298210029503584616000000000000)
      constant := (268886245953940569067997248566109804470793206810981) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (221889593340724290907/50000000000000000000)
  centralHi := (88755837336289716363/20000000000000000000)
  directionLo := (4465790831425079499/1000000000000000000)
  directionHi := (446579083142507949901/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree081.table
  base := (2757944457046921068456859603516576827079/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-4479966502014962422707922675451824000000000000)
      constant := (97962235383942660633400328765680074338367683180) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree081.table
  base := (55158888152994474413008680324261449783533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-12597587085855592078582676760364942366000000000000)
      constant := (275745904441766266486453580855786459364577797594637) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4465790831425079499/1000000000000000000)
  centralHi := (446579083142507949901/100000000000000000000)
  directionLo := (224680767128140090191/50000000000000000000)
  directionHi := (449361534256280180383/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree082.table
  base := (57325083734017086482686941421249920832153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-4535241271852649905951138631372824000000000000)
      constant := (100429975260670653722923416031076235725368283713) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree082.table
  base := (28662541445901023256860119873455949775899/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-12753018867190095263867143491226300116000000000000)
      constant := (282691942054177573076661605587513652322967186911222) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (224680767128140090191/50000000000000000000)
  centralHi := (449361534256280180383/100000000000000000000)
  directionLo := (226063431053052620819/50000000000000000000)
  directionHi := (452126862106105241639/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree083.table
  base := (59527459455107443726556815903696067896747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-4590516041690337389194354587293824000000000000)
      constant := (102928404153853752564605115782274144638831073187) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree083.table
  base := (59527458737232015286987457371264620874731/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-12908450648524598449151610222087657866000000000000)
      constant := (289724358755624516166935154894302812104622591872459) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226063431053052620819/50000000000000000000)
  centralHi := (452126862106105241639/100000000000000000000)
  directionLo := (28429711186557056347/6250000000000000000)
  directionHi := (454875378984912901553/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree084.table
  base := (30883008030884662301481969265265405455453/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-4645790811528024872437570543214824000000000000)
      constant := (105457522052698278416755636552929378232564446026) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree084.table
  base := (15441503862491391946157804835147996169831/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-13063882429859101634436076952949015616000000000000)
      constant := (296843154516178007301888365316758762205492088305436) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28429711186557056347/6250000000000000000)
  centralHi := (454875378984912901553/100000000000000000000)
  directionLo := (457607387806865700741/100000000000000000000)
  directionHi := (228803693903432850371/50000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree085.table
  base := (16010188337464592033497581831408885039229/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-4701065581365712355680786499135824000000000000)
      constant := (108017328948115520184277091867483159883326057236) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree085.table
  base := (64040752828527262943581589297451062966589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-13219314211193604819720543683810373366000000000000)
      constant := (304048329310641630776124093842757168703358444413021) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457607387806865700741/100000000000000000000)
  centralHi := (228803693903432850371/50000000000000000000)
  directionLo := (230161591248506435859/50000000000000000000)
  directionHi := (460323182497012871719/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree086.table
  base := (663516711474808060114764977846983656163/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-4756340351203399838924002455056824000000000000)
      constant := (110607824832452595408321913316319019935603292300) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree086.table
  base := (33175835351652436356294393710752096142997/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-13374745992528108005005010414671731116000000000000)
      constant := (311339883117803768021401577196604091599644151497066) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (230161591248506435859/50000000000000000000)
  centralHi := (460323182497012871719/100000000000000000000)
  directionLo := (231511524180187008303/50000000000000000000)
  directionHi := (463023048360374016607/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree087.table
  base := (17174692327475593455899626861487132563207/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-4811615121041087322167218410977824000000000000)
      constant := (113229009699265789903011287157096462515386155388) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree087.table
  base := (34349384465757042466715596390694598784413/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-13530177773862611190289477145533088866000000000000)
      constant := (318717815919807885921997132315871673206327421889914) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231511524180187008303/50000000000000000000)
  centralHi := (463023048360374016607/100000000000000000000)
  directionLo := (116426815607941104259/25000000000000000000)
  directionHi := (465707262431764417037/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree088.table
  base := (35541023857630381906097103980559979239391/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-4866889890878774805410434366898824000000000000)
      constant := (115880883543129671864644076383202333671433853422) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree088.table
  base := (8885255924119848386783297628213617432733/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-13685609555197114375573943876394446616000000000000)
      constant := (326182127701622320067393239162653030839832646827496) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116426815607941104259/25000000000000000000)
  centralHi := (465707262431764417037/100000000000000000000)
  directionLo := (58547011725947013077/12500000000000000000)
  directionHi := (468376093807576104617/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree089.table
  base := (73501506260954800187080362848698115342689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-4922164660716462288653650322819824000000000000)
      constant := (118563446359476334345865533123243124793171856969) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree089.table
  base := (14700301197292246986198504589196227240699/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-13841041336531617560858410607255804366000000000000)
      constant := (333732818450593833461748641932170095877498484714055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58547011725947013077/12500000000000000000)
  centralHi := (468376093807576104617/100000000000000000000)
  directionLo := (471029803960639383303/100000000000000000000)
  directionHi := (58878725495079922913/12500000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree090.table
  base := (18989286215150883221651329707446062704233/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-4977439430554149771896866278740824000000000000)
      constant := (121276698144460011068980864121588984630620629572) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree090.table
  base := (75957144626856268567349138585106587473849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-13996473117866120746142877338117162116000000000000)
      constant := (341369888156071714730334901770093300405013356803161) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471029803960639383303/100000000000000000000)
  centralHi := (58878725495079922913/12500000000000000000)
  directionLo := (94733729407841514939/20000000000000000000)
  directionHi := (59208580879900946837/12500000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree091.table
  base := (39224481720742650883432130038557449563851/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-5032714200391837255140082234661824000000000000)
      constant := (124020638894843061002723283072794316424064420742) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree091.table
  base := (78448963242460460143119397617854734677953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-14151904899200623931427344068978519866000000000000)
      constant := (349093336809091271015184938446749606957305381746017) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94733729407841514939/20000000000000000000)
  centralHi := (59208580879900946837/12500000000000000000)
  directionLo := (238146435075516322839/50000000000000000000)
  directionHi := (476292870151032645679/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree092.table
  base := (5061060121398813690288508722986460075607/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-5087988970229524738383298190582824000000000000)
      constant := (126795268607899949139895115322352291024417587952) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree092.table
  base := (126526502770220556818425376299623544971/15625000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-14307336680535127116711810799839877616000000000000)
      constant := (356903164402107331525273032392179211484922739084160) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (238146435075516322839/50000000000000000000)
  centralHi := (476292870151032645679/100000000000000000000)
  directionLo := (239451356816715220311/50000000000000000000)
  directionHi := (478902713633430440623/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree093.table
  base := (10442642538969734156714291861837205754479/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-5143263740067212221626514146503824000000000000)
      constant := (129600587281336383181212047094076765899161276472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree093.table
  base := (83541140167522234484203396647122451316693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-14462768461869630301996277530701235366000000000000)
      constant := (364799370928769860296687662581567967076343003749877) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239451356816715220311/50000000000000000000)
  centralHi := (478902713633430440623/100000000000000000000)
  directionLo := (481498411310170908517/100000000000000000000)
  directionHi := (240749205655085454259/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree094.table
  base := (86141498506239726584757279139963316760429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-5198538509904899704869730102424824000000000000)
      constant := (132436594913221214095261711227216162825491059509) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree094.table
  base := (8614149838347337234332925598334939376367/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-14618200243204133487280744261562593116000000000000)
      constant := (372781956383735025075165840746360842121544356964630) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (481498411310170908517/100000000000000000000)
  centralHi := (240749205655085454259/50000000000000000000)
  directionLo := (96816038147194095587/20000000000000000000)
  directionHi := (30255011920998154871/6250000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree095.table
  base := (88778036489318957043005865694925114896979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-5253813279742587188112946058345824000000000000)
      constant := (135303291501929086043216327956446541040328402059) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree095.table
  base := (88778036384838038106055384271648063819201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-14773632024538636672565210992423950866000000000000)
      constant := (380850920762506120363195923442860794725318665448289) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96816038147194095587/20000000000000000000)
  centralHi := (30255011920998154871/6250000000000000000)
  directionLo := (486648273429310130107/100000000000000000000)
  directionHi := (121662068357327532527/25000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree096.table
  base := (45725377115135819082439914142776630323917/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-5309088049580274671356162014266824000000000000)
      constant := (138200677046092139094990840246981820717302217514) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree096.table
  base := (91450754141362482498831740539147039262027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-14929063805873139857849677723285308616000000000000)
      constant := (389006264061299627736293621331071461961972033724203) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486648273429310130107/100000000000000000000)
  centralHi := (121662068357327532527/25000000000000000000)
  directionLo := (489202875094253338989/100000000000000000000)
  directionHi := (48920287509425333899/10000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree097.table
  base := (23539912925810990821016832680246005760093/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-5364362819417962154599377970187824000000000000)
      constant := (141128751544559335923994378839768557689780401812) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree097.table
  base := (94159651627593975344006268457573811046447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-15084495587207643043134144454146666366000000000000)
      constant := (397247986276932441764786889026779867597501217085583) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell143.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489202875094253338989/100000000000000000000)
  centralHi := (48920287509425333899/10000000000000000000)
  directionLo := (49174420583189251411/10000000000000000000)
  directionHi := (491744205831892514111/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 111
  qDenominator := 211
  table := BinomialMassData.Q111_211.Degree098.table
  base := (96904728886482886407408887631903895707539/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 445210000000000000000000000000000000000000000
      center := (3472638)
      previous := (1736319)
      next := (1736319)
      square := (52535929890775040379813363510500000000000000)
      linear := (-5419637589255649637842593926108824000000000000)
      constant := (144087514996362209169565490286679545340795343819) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q111_211.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 23557
  qDenominator := 44732
  table := BinomialMassData.Q23557_44732.Degree098.table
  base := (96904728822121545751598091948867246071081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1250594890000000000000000000000000000000000000000
      center := (9754640142)
      previous := (4877320071)
      next := (4877320071)
      square := (147573427063187088426895738100994500000000000000)
      linear := (-15239927368542146228418611185008024116000000000000)
      constant := (405576087406726917370180842947891362215486647537609) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q23557_44732.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell143.Kernel098
