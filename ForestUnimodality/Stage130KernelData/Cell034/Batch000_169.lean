import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell034.Parameters
import ForestUnimodality.BinomialMassData.Q9_19.Batch000_049
import ForestUnimodality.BinomialMassData.Q9_19.Batch050_099
import ForestUnimodality.BinomialMassData.Q9_19.Batch100_149
import ForestUnimodality.BinomialMassData.Q9_19.Batch150_199
import ForestUnimodality.BinomialMassData.Q1733_3648.Batch000_049
import ForestUnimodality.BinomialMassData.Q1733_3648.Batch050_099
import ForestUnimodality.BinomialMassData.Q1733_3648.Batch100_149
import ForestUnimodality.BinomialMassData.Q1733_3648.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree000.table
  base := (779340970047167317835601347/10000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (78)
      previous := (39)
      next := (39)
      square := (352723659783721818494761635000000000000)
      linear := (23158683367488202414774534000000000000)
      constant := (389670485023583658917800673500000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree000.table
  base := (779340970047167317835601347/10000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (78)
      previous := (39)
      next := (39)
      square := (352723659783721818494761635000000000000)
      linear := (23158683367488202414774534000000000000)
      constant := (389670485023583658917800673500000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree000.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree001.table
  base := (112846386416226905482393893407815573258193/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-112271206950369620853474872396000000000000)
      constant := (81499701474102466742973540287563843892415346) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree001.table
  base := (225219685366978675749480869397867988621649/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-112620256405363928903026980263968750000000)
      constant := (81329071018763966322208924912972739156087164) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree001.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (1560334371793608223/3125000000000000000)
  directionHi := (49930699897395463137/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree002.table
  base := (271815614386178018773065454167864455909059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-465805397192804965557366703132000000000000)
      constant := (98338161185526754585009528712823068583170299) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree002.table
  base := (16923943748095121283120275328180978195599/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (381999723545770729429826850705000000000000)
      linear := (-700802392519173296633362701905812500000000)
      constant := (146950053410388393442988515701250550750732236) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree002.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1560334371793608223/3125000000000000000)
  centralHi := (49930699897395463137/100000000000000000000)
  directionLo := (882658412170969617/1250000000000000000)
  directionHi := (70612672973677569361/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree003.table
  base := (42958846075976034982721617262312783204037/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-353534190242435344703891830736000000000000)
      constant := (31261542010269509015368909559362829473314714) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree003.table
  base := (170977446757834879163943599026363258192901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-709162677214836537705096308679812500000000)
      constant := (62216280225654930410374553402243875953731011) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree003.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (882658412170969617/1250000000000000000)
  centralHi := (70612672973677569361/100000000000000000000)
  directionLo := (17296501815952614109/20000000000000000000)
  directionHi := (43241254539881535273/50000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree004.table
  base := (114786216981603056054450069795722098202757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-948331363776936413258200619812000000000000)
      constant := (42320402977671386328291485791663677451195277) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree004.table
  base := (114138433576531035798405435845810058733123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-951123759416890877654617482755750000000000)
      constant := (42091760008142124481020866406421329640157403) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree004.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17296501815952614109/20000000000000000000)
  centralHi := (43241254539881535273/50000000000000000000)
  directionLo := (99861399794790926273/100000000000000000000)
  directionHi := (49930699897395463137/50000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree005.table
  base := (40554616832022793763766889630762686058647/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-594797173534501068554308789076000000000000)
      constant := (15334681413143062818107107241010329667171567) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree005.table
  base := (80636412860458606783715096620320182075979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (763999447091541458859653701410000000000000)
      linear := (-3579254524856835652812415970495062500000000)
      constant := (91520516550102130169282659366802296739066507) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree005.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99861399794790926273/100000000000000000000)
  centralHi := (49930699897395463137/50000000000000000000)
  directionLo := (13956054891839753771/12500000000000000000)
  directionHi := (111648439134718030169/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree006.table
  base := (60311253465538674849573792405776345120501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-1430857330361067860959034536492000000000000)
      constant := (23781925266648041474802471570037260588500861) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree006.table
  base := (59966360206722122139543891400023524212889/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-1435045923820999557553659830907625000000000)
      constant := (23669202941885422473695956477879076225227929) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree006.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13956054891839753771/12500000000000000000)
  centralHi := (111648439134718030169/100000000000000000000)
  directionLo := (61152368624327635029/50000000000000000000)
  directionHi := (122304737248655270059/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree007.table
  base := (5844228609007969585601389021681462067127/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-836060156826566792404725747416000000000000)
      constant := (9811305373098216600923629559425031224931388) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree007.table
  base := (4649704988971359999903757303194087071453/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-838503503011526948751590502491781250000000)
      constant := (9772989898375890139445846625515382583894540) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree007.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61152368624327635029/50000000000000000000)
  centralHi := (122304737248655270059/100000000000000000000)
  directionLo := (13210421471590666547/10000000000000000000)
  directionHi := (132104214715906665471/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree008.table
  base := (37381661029055987464169241445025081981909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-1913383296945199308659868453172000000000000)
      constant := (17088456378433391566911961668310054595469149) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree008.table
  base := (3718408434089658704579002103308924367709/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (381999723545770729429826850705000000000000)
      linear := (-2878452132337662356179053268589250000000000)
      constant := (25557212838587185737188230921048466076144235) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree008.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13210421471590666547/10000000000000000000)
  centralHi := (132104214715906665471/100000000000000000000)
  directionLo := (882658412170969617/625000000000000000)
  directionHi := (141225345947355138721/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree009.table
  base := (6104121973944956031446225699565288733143/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-2154646280237265032510285411512000000000000)
      constant := (15575097599247514652016023546533346163323115) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree009.table
  base := (30362789194255497741548672798950630453617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-2160929170427162577402223353135437500000000)
      constant := (15544741782672826732088163466652710308599487) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree009.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (882658412170969617/625000000000000000)
  centralHi := (141225345947355138721/100000000000000000000)
  directionLo := (14979209969218638941/10000000000000000000)
  directionHi := (149792099692186389411/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree010.table
  base := (25238302903119191600129963061969456217357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-2395909263529330756360702369852000000000000)
      constant := (14745947939405511975003526246090973694465877) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree010.table
  base := (784616207913729352829623906637685141007/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-1201445126314608458675872263605687500000000)
      constant := (7365846767520490300754176725705983241643932) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree010.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14979209969218638941/10000000000000000000)
  centralHi := (149792099692186389411/100000000000000000000)
  directionLo := (157894736842105263157/100000000000000000000)
  directionHi := (78947368421052631579/50000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree011.table
  base := (10501590789721142383355421733178414625791/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-1318586123410698240105559664096000000000000)
      constant := (7204557381215344634716275131858407679910551) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree011.table
  base := (10445982937026178210075077519527416543693/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (381999723545770729429826850705000000000000)
      linear := (-3967277002246906885951898551930968750000000)
      constant := (21613175668328476669445748215937360329710144) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree011.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157894736842105263157/100000000000000000000)
  centralHi := (78947368421052631579/50000000000000000000)
  directionLo := (82800698539748806341/50000000000000000000)
  directionHi := (165601397079497612683/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree012.table
  base := (17502308302846437827851048386276099747139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-2878435230113462204061536286532000000000000)
      constant := (14451627596222055054989793201189672008717179) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree012.table
  base := (17405556984857114711864365309932749060777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-2886812417033325597250786875363250000000000)
      constant := (14464111946473524441379392741895308348440497) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree012.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82800698539748806341/50000000000000000000)
  centralHi := (165601397079497612683/100000000000000000000)
  directionLo := (172965018159526141091/100000000000000000000)
  directionHi := (43241254539881535273/25000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree013.table
  base := (14543678562161201555366743296992108461169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-3119698213405527927911953244872000000000000)
      constant := (14804172812247077160300890795080151154482009) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree013.table
  base := (14458308925350614915078177083625685184437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-3128773499235379937200308049439187500000000)
      constant := (14829021953035217857283952079572721472675507) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree013.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (172965018159526141091/100000000000000000000)
  centralHi := (43241254539881535273/25000000000000000000)
  directionLo := (90013849349931945721/50000000000000000000)
  directionHi := (180027698699863891443/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree014.table
  base := (12003565545850855038094962245816892625019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-3360961196697593651762370203212000000000000)
      constant := (15422085031541360336436012336467898237631859) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree014.table
  base := (5963792850446708275188638374384637867191/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (381999723545770729429826850705000000000000)
      linear := (-5056101872156151415724743835272687500000000)
      constant := (23188863306758840021413414414931915349230353) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree014.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90013849349931945721/50000000000000000000)
  centralHi := (180027698699863891443/100000000000000000000)
  directionLo := (18682357209788261187/10000000000000000000)
  directionHi := (186823572097882611871/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree015.table
  base := (612369223469370520762079711356514076369/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-1801112089994829687806393580776000000000000)
      constant := (8137508994100264966834020324562612652553672) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree015.table
  base := (4864983662776122954145169552538279500419/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-1806347831819744308549675198795531250000000)
      constant := (8162329042981819551617608467868690725823134) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree015.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18682357209788261187/10000000000000000000)
  centralHi := (186823572097882611871/100000000000000000000)
  directionLo := (24172596145886625969/12500000000000000000)
  directionHi := (193380769167093007753/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree016.table
  base := (3933284946962674028556151448162232046519/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-1921743581640862549731602059946000000000000)
      constant := (8670631517435333230809324811122565768793359) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree016.table
  base := (7805693167124434731513680003163217100489/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-3854656745841542957048871571667000000000000)
      constant := (17403696009183291883276144078993296373276529) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree016.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24172596145886625969/12500000000000000000)
  centralHi := (193380769167093007753/100000000000000000000)
  directionLo := (199722799589581852547/100000000000000000000)
  directionHi := (49930699897395463137/25000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree017.table
  base := (96320811205159287896283803696061919451/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-2042375073286895411656810539116000000000000)
      constant := (9302283870369855938501996043673907293497952) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree017.table
  base := (3054980813517754645808324518737032960281/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (381999723545770729429826850705000000000000)
      linear := (-6144926742065395945497589118614406250000000)
      constant := (28020273895619200007652389364975400299499948) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree017.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199722799589581852547/100000000000000000000)
  centralHi := (49930699897395463137/25000000000000000000)
  directionLo := (10293477481898919023/5000000000000000000)
  directionHi := (205869549637978380461/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree018.table
  base := (4656826040533051767112547985652009045429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-4326013129865856547164038036572000000000000)
      constant := (20052308800550165123015326489396375265399869) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree018.table
  base := (4607936390202470156355996213321191988497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-4338578910245651636947913919818875000000000)
      constant := (20141541939907200673671750180625956167222417) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree018.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10293477481898919023/5000000000000000000)
  centralHi := (205869549637978380461/100000000000000000000)
  directionLo := (2647975236512908851/1250000000000000000)
  directionHi := (211838018921032708081/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree019.table
  base := (828882567514344537841902538928418344611/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (78)
      previous := (39)
      next := (39)
      square := (352723659783721818494761635000000000000)
      linear := (-6325867192739504530490934896000000000000)
      constant := (30019953427202762552026526706856836689222) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree019.table
  base := (102243075241012215680853860449579490199/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (78)
      previous := (39)
      next := (39)
      square := (352723659783721818494761635000000000000)
      linear := (-6344238216686573375204203731156250000000)
      constant := (30163052826882170983300122180401035515059) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree019.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2647975236512908851/1250000000000000000)
  centralHi := (211838018921032708081/100000000000000000000)
  directionLo := (217642875033003501599/100000000000000000000)
  directionHi := (272053593791254377/125000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree020.table
  base := (132368934252524344110371294021630523599/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-2404269548224993997432435976626000000000000)
      constant := (11731325361997067572762500364854468952153912) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree020.table
  base := (519700742292682294614983413371516356471/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (381999723545770729429826850705000000000000)
      linear := (-7233751611974640475270434401956125000000000)
      constant := (35370810029898325818644057902781395834366186) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree020.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217642875033003501599/100000000000000000000)
  centralHi := (272053593791254377/125000000000000000)
  directionLo := (223296878269436060337/100000000000000000000)
  directionHi := (111648439134718030169/50000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree021.table
  base := (522583479312738744201019874625901758513/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-2524901039871026859357644455796000000000000)
      constant := (12705131655193575630236493186980950534823193) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree021.table
  base := (1010276227553446453928177926930099784767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-5064462156851814656796477442046687500000000)
      constant := (25543226657901392050918922183068138580894637) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree021.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223296878269436060337/100000000000000000000)
  centralHi := (111648439134718030169/50000000000000000000)
  directionLo := (45762242356387700759/20000000000000000000)
  directionHi := (57202802945484625949/25000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree022.table
  base := (81674783455663098256913195245157970287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-5291065063034119442565705869932000000000000)
      constant := (27511595379492573488039252346747502027273607) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree022.table
  base := (25293403108632648015856566115388469833/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-2653211619526934498372999308061312500000000)
      constant := (13830074173974114406200727527286525354797213) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree022.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45762242356387700759/20000000000000000000)
  centralHi := (57202802945484625949/25000000000000000000)
  directionLo := (234195741697757777327/100000000000000000000)
  directionHi := (14637233856109861083/6250000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree023.table
  base := (-785694101053863816297620816965468793581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-5532328046326185166416122828272000000000000)
      constant := (29761910422296285363486024996861465765517259) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree023.table
  base := (-813353485241824822697920553084008284059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (763999447091541458859653701410000000000000)
      linear := (-16645152963767770010086559370595687500000000)
      constant := (89779740760010639089382569661369710922895353) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree023.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (234195741697757777327/100000000000000000000)
  centralHi := (14637233856109861083/6250000000000000000)
  directionLo := (59864806137249083323/25000000000000000000)
  directionHi := (239459224548996333293/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree024.table
  base := (-97999201920169022961992022837133645641/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-2886795514809125445133269893306000000000000)
      constant := (16078610139183705442667131193070358031388792) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree024.table
  base := (-398140523961327677382512235236534873843/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-2895172701728988838322520482137250000000000)
      constant := (16169272537485293982836450031305643696085354) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree024.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59864806137249083323/25000000000000000000)
  centralHi := (239459224548996333293/100000000000000000000)
  directionLo := (61152368624327635029/25000000000000000000)
  directionHi := (244609474497310540117/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree025.table
  base := (-454906622108720813401641894796135317939/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-6014854012910316614116956744952000000000000)
      constant := (34694157357403568923758329657942975751120105) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree025.table
  base := (-2296339043570636638417313645634535597047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-6032306485660032016594562138350437500000000)
      constant := (34892685506359496237140681958282512239309783) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree025.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61152368624327635029/25000000000000000000)
  centralHi := (244609474497310540117/100000000000000000000)
  directionLo := (62413374871744328921/25000000000000000000)
  directionHi := (49930699897395463137/20000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree026.table
  base := (-1456612151350230416747564413504963611673/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-3128058498101191168983686851646000000000000)
      constant := (18684936222228186165117209754620708136186047) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree026.table
  base := (-2932549804941396836543643745656596474169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (763999447091541458859653701410000000000000)
      linear := (-18822802703586259069632249937279125000000000)
      constant := (112758486331435760984552411530387220471599973) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree026.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62413374871744328921/25000000000000000000)
  centralHi := (49930699897395463137/20000000000000000000)
  directionLo := (31824701638020590733/12500000000000000000)
  directionHi := (50919522620832945173/20000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree027.table
  base := (-349074798481905109732858946250332726577/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-3248689989747224030908895330816000000000000)
      constant := (20090975734201457906680355363655149428528515) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree027.table
  base := (-3507855871062241232453485702064664129803/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-6516228650064140696493604486502312500000000)
      constant := (40416570089039081614598720545711075682734867) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree027.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31824701638020590733/12500000000000000000)
  centralHi := (50919522620832945173/20000000000000000000)
  directionLo := (259447527239289211637/100000000000000000000)
  directionHi := (129723763619644605819/50000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree028.table
  base := (-4012776095073113466960240691169886691139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-6738642962786513785668207619972000000000000)
      constant := (43128346859562479735486157910983670904498821) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree028.table
  base := (-2013952478292917485758659768018911342891/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-3379094866133097518221562830289125000000000)
      constant := (21690935308525683989452844388691434723966349) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree028.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259447527239289211637/100000000000000000000)
  centralHi := (129723763619644605819/50000000000000000000)
  directionLo := (13210421471590666547/5000000000000000000)
  directionHi := (264208429431813330941/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree029.table
  base := (-448412348900258484794107222278079851777/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-3489952973039289754759312289156000000000000)
      constant := (23103660227542573436853426887517065867542515) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree029.table
  base := (-449748922368825113899290247037077654779/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (381999723545770729429826850705000000000000)
      linear := (-10500226221702374064588970251981281250000000)
      constant := (69720500585954825555990487271573349743512340) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree029.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13210421471590666547/5000000000000000000)
  centralHi := (264208429431813330941/100000000000000000000)
  directionLo := (53777009576609687893/20000000000000000000)
  directionHi := (134442523941524219733/50000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree030.table
  base := (-4908880249487236937001380378044794612461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-7221168929370645233369041536652000000000000)
      constant := (49417395735051319645503161347685829144901579) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree030.table
  base := (-4920677635888902084084945575116423992179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-7242111896670303716342168008730125000000000)
      constant := (49710490513964120931799728060420070548198381) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree030.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53777009576609687893/20000000000000000000)
  centralHi := (134442523941524219733/50000000000000000000)
  directionLo := (68370426614560945797/25000000000000000000)
  directionHi := (273481706458243783189/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree031.table
  base := (-5290522809281582698639716283053724712059/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-7462431912662710957219458494992000000000000)
      constant := (52757317707236618870691103672419605378946701) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree031.table
  base := (-5300927093147545054250297392639880985147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-7484072978872358056291689182806062500000000)
      constant := (53071093046148607295991976091702574741705683) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree031.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68370426614560945797/25000000000000000000)
  centralHi := (273481706458243783189/100000000000000000000)
  directionLo := (11120094859995163671/4000000000000000000)
  directionHi := (4343787054685610809/1562500000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree032.table
  base := (-5632007533487753528045931403787209186397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-7703694895954776681069875453332000000000000)
      constant := (56226019123839175115607144370016817483710683) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree032.table
  base := (-45129407972894550896454955119634404399/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (763999447091541458859653701410000000000000)
      linear := (-23178102183223237188723631070646000000000000)
      constant := (169683241673127135555700158705913992504485375) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree032.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11120094859995163671/4000000000000000000)
  centralHi := (4343787054685610809/1562500000000000000)
  directionLo := (282450691894710277441/100000000000000000000)
  directionHi := (141225345947355138721/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree033.table
  base := (-2967924841935313144930737088742470339303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-3972478939623421202460146205836000000000000)
      constant := (29911295987680933916057860277316968207511617) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree033.table
  base := (-594392316970418806528583443386962634663/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-3983997571638233368095365765478968750000000)
      constant := (30089775486694962447082477543153974583105160) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree033.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282450691894710277441/100000000000000000000)
  centralHi := (141225345947355138721/50000000000000000000)
  directionLo := (17926877096629884861/6250000000000000000)
  directionHi := (286830033546078157777/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree034.table
  base := (-3102095072193052233382138875556797199427/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-4093110431269454064385354685006000000000000)
      constant := (31773131701348307931485049180107996211006853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree034.table
  base := (-1552823630204909092765970101536905368703/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-4104978112739260538070126352516937500000000)
      constant := (31962868420130328652256974159698216628483934) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree034.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17926877096629884861/6250000000000000000)
  centralHi := (286830033546078157777/100000000000000000000)
  directionLo := (291143509177670125579/100000000000000000000)
  directionHi := (14557175458883506279/5000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree035.table
  base := (-643885186753606988059304302335672238967/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-4213741922915486926310563164176000000000000)
      constant := (33698187659995119935243253381169111608664565) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree035.table
  base := (-6445099412971703600327763717897435294961/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (763999447091541458859653701410000000000000)
      linear := (-25355751923041726248269321637329437500000000)
      constant := (203396954934820063622766590610479140563838487) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree035.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291143509177670125579/100000000000000000000)
  centralHi := (14557175458883506279/5000000000000000000)
  directionLo := (147697002109497686273/50000000000000000000)
  directionHi := (295394004218995372547/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree036.table
  base := (-1660346916992599826078302428934396740777/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-4334373414561519788235771643346000000000000)
      constant := (35686183580577067169812211010765365553159006) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree036.table
  base := (-664687837180252585537236403687390504883/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-4346939194941314878019647526592875000000000)
      constant := (35899369628835602735230624589269146857436185) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree036.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147697002109497686273/50000000000000000000)
  centralHi := (295394004218995372547/100000000000000000000)
  directionLo := (14979209969218638941/5000000000000000000)
  directionHi := (299584199384372778821/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree037.table
  base := (-1362624144071662791869642951531998828619/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-8910009812415105300321960245032000000000000)
      constant := (75473761260132710409449983406278742114342705) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree037.table
  base := (-6817943493075588140210893501790463172219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-8935839472084684095988816227261687500000000)
      constant := (75924526011883592006682335662456624728422691) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree037.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14979209969218638941/5000000000000000000)
  centralHi := (299584199384372778821/100000000000000000000)
  directionLo := (60743318089488457111/20000000000000000000)
  directionHi := (75929147611860571389/25000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree038.table
  base := (-1738794724478921486588787326492201755813/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (78)
      previous := (39)
      next := (39)
      square := (352723659783721818494761635000000000000)
      linear := (-12674893068846497263396644326000000000000)
      constant := (110388020020353238575659253475015596488374) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree038.table
  base := (-6959412689251796543328154408911506347463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (468)
      previous := (234)
      next := (234)
      square := (2116341958702330910968569810000000000000)
      linear := (-76269810700443809716939091977875000000000)
      constant := (666282063777109089071820853404126809082611) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree038.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60743318089488457111/20000000000000000000)
  centralHi := (75929147611860571389/25000000000000000000)
  directionLo := (307793505625546228637/100000000000000000000)
  directionHi := (153896752812773114319/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree039.table
  base := (-706852390567298912856910480433112868959/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-4696267889499618374011397080856000000000000)
      constant := (42025593784662558400762273409207231271529005) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree039.table
  base := (-1768059682915668117717443093037858640577/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-4709880818244396387943929287706781250000000)
      constant := (42276321147553065688861499711717549606425281) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree039.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307793505625546228637/100000000000000000000)
  centralHi := (153896752812773114319/50000000000000000000)
  directionLo := (311817120917865773959/100000000000000000000)
  directionHi := (7795428022946644349/2500000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree040.table
  base := (-3576988005513278513573512696955313308497/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-4816899381145651235936605560026000000000000)
      constant := (44263288243746434829004011999839131895632583) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree040.table
  base := (-7157233892591846227282316608766363675593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-9661722718690847115837379749489500000000000)
      constant := (89054334643371214445018794366442686463110927) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree040.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311817120917865773959/100000000000000000000)
  centralHi := (7795428022946644349/2500000000000000000)
  directionLo := (63157894736842105263/20000000000000000000)
  directionHi := (78947368421052631579/25000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree041.table
  base := (-1803058761904016553056357081395446564099/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-4937530872791684097861814039196000000000000)
      constant := (46563032284627186789628564912593487580720522) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree041.table
  base := (-1443018172907963008552986740156622200517/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (763999447091541458859653701410000000000000)
      linear := (-29711051402678704367360702770696312500000000)
      constant := (281042305971944090260283806817623020178731695) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree041.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63157894736842105263/20000000000000000000)
  centralHi := (78947368421052631579/25000000000000000000)
  directionLo := (319712474704998741051/100000000000000000000)
  directionHi := (79928118676249685263/25000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree042.table
  base := (-7243898262663886192580601369559643178373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-10116324728875433919574045036732000000000000)
      constant := (97849436208362353172603624409892968812607347) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree042.table
  base := (-724640052761525084431148317378647186721/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-5072822441547477897868211048820687500000000)
      constant := (49215865514608673868652819926496974445156095) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree042.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319712474704998741051/100000000000000000000)
  centralHi := (79928118676249685263/25000000000000000000)
  directionLo := (323587918925039948943/100000000000000000000)
  directionHi := (20224244932814996809/6250000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree043.table
  base := (-3624737744527403104641665456427730963171/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-5178793856083749821712230997536000000000000)
      constant := (51348253677572699761010476934042589122295269) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree043.table
  base := (-3625833523405213139523211565152376243967/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-5193802982648505067842971635858656250000000)
      constant := (51653519877758478485519988866394397205224788) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree043.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323587918925039948943/100000000000000000000)
  centralHi := (20224244932814996809/6250000000000000000)
  directionLo := (327417495052542961177/100000000000000000000)
  directionHi := (163708747526271480589/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree044.table
  base := (-7229402048761890512788263718165601391379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-10598850695459565367274878953412000000000000)
      constant := (107667120858371236433094990718430217897712181) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree044.table
  base := (-903915088249525815347738832081487727757/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (381999723545770729429826850705000000000000)
      linear := (-15944350571248596713453196668689875000000000)
      constant := (162459809255604213189244140805649311569606676) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree044.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327417495052542961177/100000000000000000000)
  centralHi := (163708747526271480589/50000000000000000000)
  directionLo := (66240558831799045073/20000000000000000000)
  directionHi := (165601397079497612683/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree045.table
  base := (-7184049731391172235941145220052486669531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-10840113678751631091125295911752000000000000)
      constant := (112761142501992085944868420859051052312299309) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree045.table
  base := (-3592864411226841764279236376294476989199/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-5435764064850559407792492809934593750000000)
      constant := (56715048836168214503813179009506227742446036) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree045.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66240558831799045073/20000000000000000000)
  centralHi := (165601397079497612683/50000000000000000000)
  directionLo := (66989063480830818101/20000000000000000000)
  directionHi := (167472658702077045253/50000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree046.table
  base := (-7113736138691349847839584192315401643877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-11081376662043696814975712870092000000000000)
      constant := (117978457631776667909997007522606140006560403) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree046.table
  base := (-7115205032698543699394551496663110975967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-11113489211903173155534506793945125000000000)
      constant := (118677601038535654823941112588171997797050913) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree046.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66989063480830818101/20000000000000000000)
  centralHi := (167472658702077045253/50000000000000000000)
  directionLo := (338646482992534999099/100000000000000000000)
  directionHi := (3386464829925349991/1000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree047.table
  base := (-701873264125205370287146968384696727311/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-5661319822667881269413064914216000000000000)
      constant := (61659484141471062885273361381222622407203645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree047.table
  base := (-219375537363659986155766848883832066729/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (381999723545770729429826850705000000000000)
      linear := (-17033175441157841243226041952031593750000000)
      constant := (186073429357902950302163022949733682801235513) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree047.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338646482992534999099/100000000000000000000)
  centralHi := (3386464829925349991/1000000000000000000)
  directionLo := (4278845405660289359/1250000000000000000)
  directionHi := (342307632452823148721/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree048.table
  base := (-1724817788990544515605802449926091352947/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-5781951314313914131338273393386000000000000)
      constant := (64391295366745784349078536626321362043172266) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree048.table
  base := (-6900394121377357061651950250264220827787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-11597411376307281835433549142097000000000000)
      constant := (129544070672086396648452277421334991281168893) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree048.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4278845405660289359/1250000000000000000)
  centralHi := (342307632452823148721/100000000000000000000)
  directionLo := (345930036319052282183/100000000000000000000)
  directionHi := (43241254539881535273/12500000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree049.table
  base := (-1688887480251432830761088359139060304343/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-5902582805959946993263481872556000000000000)
      constant := (67184626709720284830836835920750598460264354) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree049.table
  base := (-6756531302183883926788388859657433166947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-11839372458509336175383070316172937500000000)
      constant := (135162883766281413560437529870786722779075883) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree049.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (345930036319052282183/100000000000000000000)
  centralHi := (43241254539881535273/12500000000000000000)
  directionLo := (349514899281768241957/100000000000000000000)
  directionHi := (174757449640884120979/50000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree050.table
  base := (-6587738418306609477732145291775423429401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-12046428595211959710377380703452000000000000)
      constant := (140078895157814602207624513193269072141986239) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree050.table
  base := (-131771915903563477635377847138696176537/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (381999723545770729429826850705000000000000)
      linear := (-18122000311067085772998887235373312500000000)
      constant := (211357997820349248381640076239404591059323225) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree050.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349514899281768241957/100000000000000000000)
  centralHi := (174757449640884120979/50000000000000000000)
  directionLo := (353063364868387846801/100000000000000000000)
  directionHi := (176531682434193923401/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree051.table
  base := (-6395981570616931976495503795020863919969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-12287691578504025434227797661792000000000000)
      constant := (145911463631500151214556377754839468124891191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree051.table
  base := (-6396730383659187038229449812923359715837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-12323294622913444855282112664324812500000000)
      constant := (146771363469169728130119248233215453763676593) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree051.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353063364868387846801/100000000000000000000)
  centralHi := (176531682434193923401/50000000000000000000)
  directionLo := (178288259852150761971/50000000000000000000)
  directionHi := (356576519704301523943/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree052.table
  base := (-6180403321223255132574661551231048972027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-12528954561796091158078214620132000000000000)
      constant := (151866914096970769853389541555829591321098253) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree052.table
  base := (-6181057124700408110816330344399183924139/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-12565255705115499195231633838400750000000000)
      constant := (152760934470488573205527818940467730540885821) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree052.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (178288259852150761971/50000000000000000000)
  centralHi := (356576519704301523943/100000000000000000000)
  directionLo := (72011079479945556577/20000000000000000000)
  directionHi := (180027698699863891443/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree053.table
  base := (-1485277421993298058852545822896496677599/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-6385108772544078440964315789236000000000000)
      constant := (78972604140891734863317980364141729398773522) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree053.table
  base := (-5941680374415214518764713155894640748087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (763999447091541458859653701410000000000000)
      linear := (-38421650361952660605543465037430062500000000)
      constant := (476622021634897314696925589765571127995603029) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree053.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72011079479945556577/20000000000000000000)
  centralHi := (180027698699863891443/50000000000000000000)
  directionLo := (45437622762715808767/12500000000000000000)
  directionHi := (363500982101726470137/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree054.table
  base := (-1135638273908289714191296575005311732213/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-13011480528380222605779048536812000000000000)
      constant := (164146313443716682226066091869123412323355535) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree054.table
  base := (-5678689368511563610949005510730030773133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-13049177869519607875130676186552625000000000)
      constant := (165110549478510750607517720155324761625273987) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree054.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45437622762715808767/12500000000000000000)
  centralHi := (363500982101726470137/100000000000000000000)
  directionLo := (183457105872982905087/50000000000000000000)
  directionHi := (14676568469838632407/4000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree055.table
  base := (-5391725970172030293267472686375757614611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-13252743511672288329629465495152000000000000)
      constant := (170470201567638321130066472607428351501125429) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree055.table
  base := (-5392160424090454564081358559918187810729/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-13291138951721662215080197360628562500000000)
      constant := (171470533720650049628362303075355254415170581) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree055.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (183457105872982905087/50000000000000000000)
  centralHi := (14676568469838632407/4000000000000000000)
  directionLo := (370295981038691806939/100000000000000000000)
  directionHi := (18514799051934590347/5000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree056.table
  base := (-508177989922676493114317046385669928437/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-6747003247482177026739941226746000000000000)
      constant := (88458424339884383350370148269849865779171215) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree056.table
  base := (-5082158818753605882957736260364769436267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (763999447091541458859653701410000000000000)
      linear := (-40599300101771149665089155604113500000000000)
      constant := (533861809118508344743832807080516735950522839) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree056.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370295981038691806939/100000000000000000000)
  centralHi := (18514799051934590347/5000000000000000000)
  directionLo := (373647144195765223741/100000000000000000000)
  directionHi := (186823572097882611871/50000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree057.table
  base := (-2374204996732524377946714086739722457909/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (78)
      previous := (39)
      next := (39)
      square := (352723659783721818494761635000000000000)
      linear := (-19023918944953489996302353756000000000000)
      constant := (254136058534678499839535605410260277542091) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree057.table
  base := (-949748078939826159560653997012888782751/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (156)
      previous := (78)
      next := (78)
      square := (705447319567443636989523270000000000000)
      linear := (-38158064033589393060884320522937500000000)
      constant := (511248579712009494709563284166550302179995) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree057.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (373647144195765223741/100000000000000000000)
  centralHi := (186823572097882611871/50000000000000000000)
  directionLo := (376968517462525956283/100000000000000000000)
  directionHi := (94242129365631489071/25000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree058.table
  base := (-219583245142240504795441471427957410827/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-6988266230774242750590358185086000000000000)
      constant := (95089170375905419776865351811273073746914530) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree058.table
  base := (-4391952928367899029404289278643480887129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-14017022198327825234928760882856375000000000)
      constant := (191290919182952833685782667781602412384121431) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree058.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (376968517462525956283/100000000000000000000)
  centralHi := (94242129365631489071/25000000000000000000)
  directionLo := (2970788136215204477/781250000000000000)
  directionHi := (380260881435546173057/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree059.table
  base := (-1002896568643788242264848360746158825631/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-7108897722420275612515566664256000000000000)
      constant := (98496576557222584079523604576250273327894418) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree059.table
  base := (-160473492006494026331306060675146010471/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (763999447091541458859653701410000000000000)
      linear := (-42776949841589638724634846170796937500000000)
      constant := (594433402007289156997300535319850273817278925) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree059.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2970788136215204477/781250000000000000)
  centralHi := (380260881435546173057/100000000000000000000)
  directionLo := (383524983204982712203/100000000000000000000)
  directionHi := (95881245801245678051/25000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree060.table
  base := (-3608209765002549299117355866808467035093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-14459058428132616948881550286852000000000000)
      constant := (203930658477999786335612446626402143400331427) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree060.table
  base := (-902107123407237947602173911392588248027/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-7250472181365966957413901615504125000000000)
      constant := (102560684552702904632924792599866875503674506) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree060.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383524983204982712203/100000000000000000000)
  centralHi := (95881245801245678051/25000000000000000000)
  directionLo := (24172596145886625969/6250000000000000000)
  directionHi := (77352307666837203101/20000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree061.table
  base := (-1590782952267944528705636590158031081529/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-7350160705712341336365983622596000000000000)
      constant := (105495422910498542401888403577433950779568031) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree061.table
  base := (-3181756449136122380441472279809675748543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-14742905444933988254777324405084187500000000)
      constant := (212221613683408104882398970788905509300869727) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree061.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24172596145886625969/6250000000000000000)
  centralHi := (77352307666837203101/20000000000000000000)
  directionLo := (194985616345712668887/50000000000000000000)
  directionHi := (15598849307657013511/4000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree062.table
  base := (-546336167418762312113593844914558084331/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-14941584394716748396582384203532000000000000)
      constant := (218173705705482434770238007331273222657782545) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree062.table
  base := (-2731846793373807179554418878565312685879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (763999447091541458859653701410000000000000)
      linear := (-44954599581408127784180536737480375000000000)
      constant := (658335575455604607380724172854333002689318043) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree062.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (194985616345712668887/50000000000000000000)
  centralHi := (15598849307657013511/4000000000000000000)
  directionLo := (39315472414701260131/10000000000000000000)
  directionHi := (393154724147012601311/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree063.table
  base := (-2258576952391292039086302124071040006727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-15182847378008814120432801161872000000000000)
      constant := (225479230048768730176785959372676354557571553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree063.table
  base := (-282340182856197261212958876840757232981/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-7613413804669048467338183376618031250000000)
      constant := (113396047795853434271385340372768685569247311) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree063.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39315472414701260131/10000000000000000000)
  centralHi := (393154724147012601311/100000000000000000000)
  directionLo := (39631264414771999641/10000000000000000000)
  directionHi := (396312644147719996411/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree064.table
  base := (-1762273426687487066565513643786535736451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-15424110361300879844283218120212000000000000)
      constant := (232907411928226415500351337001921060599141189) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree064.table
  base := (-1762399236875252866885948465190738775343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-15468788691540151274625887927312000000000000)
      constant := (234262318223592536920072024331724143302101177) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree064.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39631264414771999641/10000000000000000000)
  centralHi := (396312644147719996411/100000000000000000000)
  directionLo := (199722799589581852547/50000000000000000000)
  directionHi := (79889119835832741019/20000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree065.table
  base := (-621393342661137861298885327673548474347/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-7832686672296472784066817539276000000000000)
      constant := (120229122707153897196600683989174849000760733) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree065.table
  base := (-621448096628206459900326839663367184371/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (381999723545770729429826850705000000000000)
      linear := (-23566124660613308421863113652081906250000000)
      constant := (362783780865156089055407406138674540380341832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree065.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199722799589581852547/50000000000000000000)
  centralHi := (79889119835832741019/20000000000000000000)
  directionLo := (402554172125746170791/100000000000000000000)
  directionHi := (50319271515718271349/12500000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree066.table
  base := (-350065399207283957660310379788728393599/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-7953318163942505645992026018446000000000000)
      constant := (124065862713849970189249198809032269049910761) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree066.table
  base := (-700226097954721460715092693610351097247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-15952710855944259954524930275463875000000000)
      constant := (249572697681729275473740922548546075363268833) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree066.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (402554172125746170791/100000000000000000000)
  centralHi := (50319271515718271349/12500000000000000000)
  directionLo := (405638923536793548003/100000000000000000000)
  directionHi := (101409730884198387001/25000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree067.table
  base := (-134317819430265498314430412856713524757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-16147899311177077015834468995232000000000000)
      constant := (255927847617101662887099913630312726417562723) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree067.table
  base := (-134400738338600758758080152279455208639/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-16194671938146314294474451449539812500000000)
      constant := (257412845283228184791324477613443418915775071) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree067.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405638923536793548003/100000000000000000000)
  centralHi := (101409730884198387001/25000000000000000000)
  directionLo := (81740078561335481499/20000000000000000000)
  directionHi := (51087549100834675937/12500000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree068.table
  base := (227320962545754125480311845216069673767/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-8194581147234571369842442976786000000000000)
      constant := (131923304127316169207921396114211001152229887) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree068.table
  base := (454569791771588457023367589665720728959/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (763999447091541458859653701410000000000000)
      linear := (-49309899061045105903271917870847250000000000)
      constant := (796128879212194911299508889148959920861962597) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree068.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (81740078561335481499/20000000000000000000)
  centralHi := (51087549100834675937/12500000000000000000)
  directionLo := (411739099275956760921/100000000000000000000)
  directionHi := (205869549637978380461/50000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree069.table
  base := (106673958757535433571799313335106382051/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-8315212638880604231767651455956000000000000)
      constant := (135944002073158623963443544716938867019602055) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree069.table
  base := (66667303016178559742683554858979921863/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-8339297051275211487186746898845843750000000)
      constant := (136731518961856699643488479813953959356137219) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree069.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (411739099275956760921/100000000000000000000)
  centralHi := (205869549637978380461/50000000000000000000)
  directionLo := (41475554325990622569/10000000000000000000)
  directionHi := (414755543259906225691/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree070.table
  base := (1701967587163166221932520225138014827651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-16871688261053274187385719870252000000000000)
      constant := (280052032555466614961449723320314823352782011) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree070.table
  base := (850956514042161884013048218177683332673/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-8460277592376238657161507485883812500000000)
      constant := (140836538584838217661325320778857998175282453) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree070.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41475554325990622569/10000000000000000000)
  centralHi := (414755543259906225691/100000000000000000000)
  directionLo := (417750207010198514289/100000000000000000000)
  directionHi := (41775020701019851429/10000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree071.table
  base := (2360319428018174305175125775484986511/10000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-8556475622172669955618068414296000000000000)
      constant := (144169345568541682846165898150016040065235500) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree071.table
  base := (590067997693367024649140933097501921893/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (381999723545770729429826850705000000000000)
      linear := (-25743774400431797481408804218765343750000000)
      constant := (435009612779564164799871336266936824172585863) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree071.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417750207010198514289/100000000000000000000)
  centralHi := (41775020701019851429/10000000000000000000)
  directionLo := (210361777807487807431/50000000000000000000)
  directionHi := (420723555614975614863/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree072.table
  base := (608357908752921821760077526097184199579/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-17354214227637405635086553786932000000000000)
      constant := (296747977881705847338464310975469417480240095) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree072.table
  base := (3041748305650755837933844847381676683179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-17404477349156585994222057319919500000000000)
      constant := (298463030013338555105180269184067379032627619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree072.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (210361777807487807431/50000000000000000000)
  centralHi := (420723555614975614863/100000000000000000000)
  directionLo := (423676037842065416161/100000000000000000000)
  directionHi := (211838018921032708081/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree073.table
  base := (468296645536175488846751229198678404617/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-8797738605464735679468485372636000000000000)
      constant := (152639945533661621406596443253155891616266948) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree073.table
  base := (374633732109493644166097122925305280027/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-8823219215679320167085789246997718750000000)
      constant := (153521469985664249795964345464372286137870610) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree073.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423676037842065416161/100000000000000000000)
  centralHi := (211838018921032708081/50000000000000000000)
  directionLo := (213304043464836253119/50000000000000000000)
  directionHi := (426608086929672506239/100000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree074.table
  base := (223703310083993687219373591290006017909/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-8918370097110768541393693851806000000000000)
      constant := (156967214609099536421767873485380921724651490) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree074.table
  base := (1118508763157399011389217467551108995383/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (381999723545770729429826850705000000000000)
      linear := (-26832599270341042011181649502107062500000000)
      constant := (473619205432924936882763523084260656185562078) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree074.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213304043464836253119/50000000000000000000)
  centralHi := (426608086929672506239/100000000000000000000)
  directionLo := (429520121328487684579/100000000000000000000)
  directionHi := (21476006066424384229/5000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree075.table
  base := (5224865152538884793044234835959170039521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-18078003177513602806637804661952000000000000)
      constant := (322711591069606972121701541872431260384267081) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree075.table
  base := (5224838087126462694588202328474607611891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-18130360595762749014070620842147312500000000)
      constant := (324572619733063623919154207388879174656486401) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree075.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (429520121328487684579/100000000000000000000)
  centralHi := (21476006066424384229/5000000000000000000)
  directionLo := (432412545398815352729/100000000000000000000)
  directionHi := (43241254539881535273/10000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree076.table
  base := (5998767014318430145389748336253446742171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (156)
      previous := (78)
      next := (78)
      square := (705447319567443636989523270000000000000)
      linear := (-50745889642120965458416126372000000000000)
      constant := (918591067971266233109948139808253446742171) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree076.table
  base := (5998743500794200415700054614684540074859/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (156)
      previous := (78)
      next := (78)
      square := (705447319567443636989523270000000000000)
      linear := (-50892857833697516216122277053250000000000)
      constant := (923884729222107549300807321265082977574859) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree076.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432412545398815352729/100000000000000000000)
  centralHi := (43241254539881535273/10000000000000000000)
  directionLo := (217642875033003501599/50000000000000000000)
  directionHi := (435285750066007003199/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree077.table
  base := (6795769213653770419016269725292549524319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-18560529144097734254338638578632000000000000)
      constant := (340633781693274816019455761686704610378279159) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree077.table
  base := (3397874394481483428902556558126088557027/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (381999723545770729429826850705000000000000)
      linear := (-27921424140250286540954494785448781250000000)
      constant := (513893157899173623452617302908218483838900866) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree077.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217642875033003501599/50000000000000000000)
  centralHi := (435285750066007003199/100000000000000000000)
  directionLo := (219070056718604336001/50000000000000000000)
  directionHi := (438140113437208672003/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree078.table
  base := (1903967386242977814874508991598431454397/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-9400896063694899989094527768486000000000000)
      constant := (174889404370169119380023645531982067510074634) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree078.table
  base := (7615851805963329063480048821665133574689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-18856243842368912033919184364375125000000000)
      constant := (351791773009281729633984662502075306579837729) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree078.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (219070056718604336001/50000000000000000000)
  centralHi := (438140113437208672003/100000000000000000000)
  directionLo := (17639040055287083583/4000000000000000000)
  directionHi := (55122000172772136197/12500000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree079.table
  base := (1057383264737180251526702126809857864097/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-9521527555340932851019736247656000000000000)
      constant := (179523227998195927564073765178142434755756068) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree079.table
  base := (4229525356822229756864326188719451645929/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-9549102462285483186934352769225531250000000)
      constant := (180555694907553159279976596544938000120352244) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree079.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17639040055287083583/4000000000000000000)
  centralHi := (55122000172772136197/12500000000000000000)
  directionLo := (221896884040345200229/50000000000000000000)
  directionHi := (443793768080690400459/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree080.table
  base := (9325357312191845201903664662281060476177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-19284318093973931425889889453652000000000000)
      constant := (368436722876529560315187854860843462831899897) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree080.table
  base := (9325343937287025800302964464888775852041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (763999447091541458859653701410000000000000)
      linear := (-58020498020319062141454680137581000000000000)
      constant := (1111662865345347510240818841164507669247760403) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree080.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (221896884040345200229/50000000000000000000)
  centralHi := (443793768080690400459/100000000000000000000)
  directionLo := (223296878269436060337/50000000000000000000)
  directionHi := (17863750261554884827/4000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree081.table
  base := (10214741739144585800870179704597323723443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-19525581077265997149740306411992000000000000)
      constant := (377949608879426851176169286864561633864162923) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree081.table
  base := (2553682531961522041776031784592051435689/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-9791063544487537526883873943301468750000000)
      constant := (190060234211152530471496118339288286087739333) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree081.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223296878269436060337/50000000000000000000)
  centralHi := (17863750261554884827/4000000000000000000)
  directionLo := (449376299076559168231/100000000000000000000)
  directionHi := (56172037384569896029/12500000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree082.table
  base := (5563609104245053168139056921343495979519/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-9883422030279031436795361685166000000000000)
      constant := (193792556787698930731699186965797002048606359) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree082.table
  base := (1112720812961310175195817845347097155167/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-9912044085588564696858634530339437500000000)
      constant := (194904964659731603226433130849583700794763935) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree082.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449376299076559168231/100000000000000000000)
  centralHi := (56172037384569896029/12500000000000000000)
  directionLo := (22607085889383715507/5000000000000000000)
  directionHi := (452141717787674310141/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree083.table
  base := (12062785700058130675711661125719140809727/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-20008107043850128597441140328672000000000000)
      constant := (397343236596161121493073010113690609832311447) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree083.table
  base := (12062776952517597990359564396213468163249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (763999447091541458859653701410000000000000)
      linear := (-60198147760137551201000370704264437500000000)
      constant := (1198868012347524502374325551352680889634079917) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree083.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22607085889383715507/5000000000000000000)
  centralHi := (452141717787674310141/100000000000000000000)
  directionLo := (454890324975408426173/100000000000000000000)
  directionHi := (227445162487704213087/50000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree084.table
  base := (6510721669739347131078398747888032110467/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-10124685013571097160645778643506000000000000)
      constant := (203611988813034537030055566362971579591878587) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree084.table
  base := (13021435748401544891653442617734417290479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-20308010335581238073616311408830750000000000)
      constant := (409558692505254894410092604845816335579362919) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree084.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (454890324975408426173/100000000000000000000)
  centralHi := (227445162487704213087/50000000000000000000)
  directionLo := (457622423563877007591/100000000000000000000)
  directionHi := (57202802945484625949/12500000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree085.table
  base := (700159518868043495956027520443252179821/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-10245316505217130022570987122676000000000000)
      constant := (208613668197295797226899389339985140369153810) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree085.table
  base := (14003183790695533787570250432241161593667/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-20549971417783292413565832582906687500000000)
      constant := (419617994225411830779573212754364369393907537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree085.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457622423563877007591/100000000000000000000)
  centralHi := (57202802945484625949/12500000000000000000)
  directionLo := (460338307487786879279/100000000000000000000)
  directionHi := (5754228843597335991/1250000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree086.table
  base := (15008026171447635172766357996806400788789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-20731895993726325768992391203692000000000000)
      constant := (427353312669873897561080949141359110684752829) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree086.table
  base := (15008020457008178870315827597771817429701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (763999447091541458859653701410000000000000)
      linear := (-62375797499956040260546061270947875000000000)
      constant := (1289401727154887058869809946987568473979491183) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree086.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460338307487786879279/100000000000000000000)
  centralHi := (5754228843597335991/1250000000000000000)
  directionLo := (463038262061532004579/100000000000000000000)
  directionHi := (23151913103076600229/5000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree087.table
  base := (4008987542830192381837339516341101959563/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-10486579488509195746421404081016000000000000)
      constant := (218800953126607502891496874428995275614804486) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree087.table
  base := (4008986303552616717951626782655045100533/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-10516946791093700546732437465529281250000000)
      constant := (220053218395723443575702354894586880795006701) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree087.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463038262061532004579/100000000000000000000)
  centralHi := (23151913103076600229/5000000000000000000)
  directionLo := (93144512865806057901/20000000000000000000)
  directionHi := (232861282164515144753/50000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree088.table
  base := (8543480952645410474735727313840308569489/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-10607210980155228608346612560186000000000000)
      constant := (223986558487167513467740232589304351393585529) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree088.table
  base := (3417391521131396706977892107070651673317/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-21275854664389455433414396105134500000000000)
      constant := (450535577280016438817145224047465870020337185) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree088.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93144512865806057901/20000000000000000000)
  centralHi := (232861282164515144753/50000000000000000000)
  directionLo := (93678296679103110931/20000000000000000000)
  directionHi := (14637233856109861083/3125000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree089.table
  base := (18161060969159528830918796587637130316557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-21455684943602522940543642078712000000000000)
      constant := (458466944687318388938975897857515004044277077) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree089.table
  base := (9080528620118722515940591609148126010137/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (381999723545770729429826850705000000000000)
      linear := (-32276723619887264660045875918815656250000000)
      constant := (691631995564220293238046669918623821103743996) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree089.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93678296679103110931/20000000000000000000)
  centralHi := (14637233856109861083/3125000000000000000)
  directionLo := (471045280742409403091/100000000000000000000)
  directionHi := (117761320185602350773/25000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree090.table
  base := (9629123508293454103049298082744672986353/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-10848473963447294332197029518526000000000000)
      constant := (234541694633568178610450525253110826948073433) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree090.table
  base := (9629121891498017594740240842203937895979/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-10879888414396782056656719226643187500000000)
      constant := (235881847979459553768750323316156944822635919) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree090.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471045280742409403091/100000000000000000000)
  centralHi := (117761320185602350773/25000000000000000000)
  directionLo := (473684210526315789473/100000000000000000000)
  directionHi := (236842105263157894737/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree091.table
  base := (5094629937708393612090973646752595828783/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-10969105455093327194122237997696000000000000)
      constant := (239911225303333006965518185503616374188381326) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree091.table
  base := (20378516947093768891168712171639556141979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-22001737910995618453262959627362312500000000)
      constant := (482562673924784301326490593709060361700848169) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree091.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (473684210526315789473/100000000000000000000)
  centralHi := (236842105263157894737/50000000000000000000)
  directionLo := (476308519863105981671/100000000000000000000)
  directionHi := (59538564982888247709/12500000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree092.table
  base := (21521878917681748697082735432436408868759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-22179473893478720112094892953732000000000000)
      constant := (490684128614134740900693723093013543601621999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree092.table
  base := (5380469121730346864987951265981075530861/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (381999723545770729429826850705000000000000)
      linear := (-33365548489796509189818721202157375000000000)
      constant := (740227396277616251714909143066882669756094926) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree092.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476308519863105981671/100000000000000000000)
  centralHi := (59538564982888247709/12500000000000000000)
  directionLo := (59864806137249083323/12500000000000000000)
  directionHi := (95783689819598533317/20000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree093.table
  base := (1418020268710407921629153184516573543827/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-11210368438385392917972654956036000000000000)
      constant := (250834211605464703855719498852996864394572376) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree093.table
  base := (11344161096098964350887923518057381067699/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-11242830037699863566581000987757093750000000)
      constant := (252265233331943639817896844464259975063486214) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree093.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59864806137249083323/12500000000000000000)
  centralHi := (95783689819598533317/20000000000000000000)
  directionLo := (120378558015607154501/25000000000000000000)
  directionHi := (96302846412485723601/20000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree094.table
  base := (23877855709373097814922286027078060926003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-22661999860062851559795726870412000000000000)
      constant := (512775334329718167671550410248063179994287083) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree094.table
  base := (23877853882913774085265285451047488508453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-22727621157601781473111523149590125000000000)
      constant := (515699281296230164514226799858838867960926533) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree094.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (120378558015607154501/25000000000000000000)
  centralHi := (96302846412485723601/20000000000000000000)
  directionLo := (484096096318607104943/100000000000000000000)
  directionHi := (30256006019912944059/6250000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree095.table
  base := (25090472987976245944229453682033097149643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (156)
      previous := (78)
      next := (78)
      square := (705447319567443636989523270000000000000)
      linear := (-63443941394334950924227545232000000000000)
      constant := (1451537013608975672630684367372033097149643) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree095.table
  base := (12545235702498616159428491650392377824087/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 15000000000000000000000000000000000000000
      center := (234)
      previous := (117)
      next := (117)
      square := (1058170979351165455484284905000000000000)
      linear := (-95441477450708459057040350375343750000000)
      constant := (2189714853295649343029021339511134408862886) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree095.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (484096096318607104943/100000000000000000000)
  centralHi := (30256006019912944059/6250000000000000000)
  directionLo := (486664263392287614493/100000000000000000000)
  directionHi := (243332131696143807247/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree096.table
  base := (26326175998416153080738874548827614942133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-23144525826646983007496560787092000000000000)
      constant := (535357005910925263838596019173758768994110013) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree096.table
  base := (6581543656650265809770488528943816508363/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-11605771661002945076505282748871000000000000)
      constant := (269203373403529379030527196181767185519038086) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree096.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486664263392287614493/100000000000000000000)
  centralHi := (243332131696143807247/50000000000000000000)
  directionLo := (489218948994621080233/100000000000000000000)
  directionHi := (244609474497310540117/50000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree097.table
  base := (3448120577952459349947592427166137592867/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-11692894404969524365673488872716000000000000)
      constant := (273415883140854950295464648390284902684099948) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree097.table
  base := (68962408587300495611346277604265142599/25000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-11726752202103972246480043335908968750000000)
      constant := (274972698798612491632665280433997979184319675) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree097.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489218948994621080233/100000000000000000000)
  centralHi := (244609474497310540117/50000000000000000000)
  directionLo := (98352072646720654529/20000000000000000000)
  directionHi := (245880181616801636323/50000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree098.table
  base := (28866838763389241192728551975815100392387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-23627051793231114455197394703772000000000000)
      constant := (558429142989022805339879324273205251241651707) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree098.table
  base := (5773367546692926513094243100384646116471/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (763999447091541458859653701410000000000000)
      linear := (-71086396459229996498728823537681625000000000)
      constant := (1684821981086456177339793783688677157548815465) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree098.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98352072646720654529/20000000000000000000)
  centralHi := (245880181616801636323/50000000000000000000)
  directionLo := (247144355407871492761/50000000000000000000)
  directionHi := (494288710815742985523/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree099.table
  base := (1885737395749541148823906541496534929031/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-11934157388261590089523905831056000000000000)
      constant := (285074568000957328047563585561190992875041528) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree099.table
  base := (7542949359930589402139565933750772193537/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-11968713284306026586429564509984906250000000)
      constant := (286696267536026575251333661145174849271780589) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree099.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247144355407871492761/50000000000000000000)
  centralHi := (494288710815742985523/100000000000000000000)
  directionLo := (15525130976202901189/3125000000000000000)
  directionHi := (496804191238492838049/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree100.table
  base := (15749921628048308564514367217286967855381/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-12054788879907622951449114310226000000000000)
      constant := (290995872646956064111253966384040595395792541) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree100.table
  base := (31499842483156531250430900171965731426839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-24179387650814107512808650194045750000000000)
      constant := (585301021701464457427002623289966152482588879) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree100.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15525130976202901189/3125000000000000000)
  centralHi := (496804191238492838049/100000000000000000000)
  directionLo := (62413374871744328921/12500000000000000000)
  directionHi := (499306998973954631369/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree101.table
  base := (3285097347299488249531927131022963889501/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-12175420371553655813374322789396000000000000)
      constant := (296978485421189135454169696024217449820549305) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree101.table
  base := (32850972803489075127996555068502442844687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (763999447091541458859653701410000000000000)
      linear := (-73264046199048485558274514104365062500000000)
      constant := (1791998360685876780791582239652138903901577271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree101.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62413374871744328921/12500000000000000000)
  centralHi := (499306998973954631369/100000000000000000000)
  directionLo := (501797323644338002177/100000000000000000000)
  directionHi := (250898661822169001089/50000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree102.table
  base := (17112594464544568924137832158286968288477/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-12296051863199688675299531268566000000000000)
      constant := (303022406313982045924274764080853595552140197) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree102.table
  base := (34225188349229733109271403429565704856131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-24663309815218216192707692542197625000000000)
      constant := (609487830634948576549595531249377990937438291) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree102.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (501797323644338002177/100000000000000000000)
  centralHi := (250898661822169001089/50000000000000000000)
  directionLo := (252137675094810189459/50000000000000000000)
  directionHi := (504275350189620378919/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree103.table
  base := (7124497915717291054551757705261257177809/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-24833366709691443074449479495472000000000000)
      constant := (618255270634138344065773117009142569205945245) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree103.table
  base := (35622489076415488906392936338574980669801/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-24905270897420270532657213716273562500000000)
      constant := (621766152904562757404288611667075647611641911) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree103.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252137675094810189459/50000000000000000000)
  centralHi := (504275350189620378919/100000000000000000000)
  directionLo := (63342657378478470489/12500000000000000000)
  directionHi := (506741259027827763913/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree104.table
  base := (37042875382382505762583172936357628890321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-25074629692983508798299896453812000000000000)
      constant := (630588344846784364788777203558633104029405881) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree104.table
  base := (740857498950605283362120620748990231729/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (381999723545770729429826850705000000000000)
      linear := (-37720847969433487308910102335524250000000000)
      constant := (951251630535887247814705332732208176149062675) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree104.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63342657378478470489/12500000000000000000)
  centralHi := (506741259027827763913/100000000000000000000)
  directionLo := (31824701638020590733/6250000000000000000)
  directionHi := (509195226208329451729/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree105.table
  base := (9621586576776007339336333359754350567281/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-12657946338137787261075156706076000000000000)
      constant := (321522017626927203585928065023647641109576882) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree105.table
  base := (38486345930579122021644849500590078096861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-25389193061824379212556256064425437500000000)
      constant := (646692632981484627755071894185326082157810571) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree105.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31824701638020590733/6250000000000000000)
  centralHi := (509195226208329451729/100000000000000000000)
  directionLo := (31977338972407205087/6250000000000000000)
  directionHi := (511637423558515281393/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree106.table
  base := (19976451162143931347338221767403024868267/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-12778577829783820123000365185246000000000000)
      constant := (327811170922536634620597375054408491977444387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree106.table
  base := (39952901998294888218824498769436284063481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-25631154144026433552505777238501375000000000)
      constant := (659340790767398695136498882400597238781291641) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree106.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31977338972407205087/6250000000000000000)
  centralHi := (511637423558515281393/100000000000000000000)
  directionLo := (514068018824201254337/100000000000000000000)
  directionHi := (257034009412100627169/50000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree107.table
  base := (41442543409677059357753163060237880874587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-25798418642859705969851147328832000000000000)
      constant := (668323264611684193340319837944179874995725907) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree107.table
  base := (20721271563729130608021474166255882074483/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (381999723545770729429826850705000000000000)
      linear := (-38809672839342731838682947618865968750000000)
      constant := (1008168340559927299245266280178963929124555714) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree107.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (514068018824201254337/100000000000000000000)
  centralHi := (257034009412100627169/50000000000000000000)
  directionLo := (16140224243877755981/3125000000000000000)
  directionHi := (516487175804088191393/100000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree108.table
  base := (42955269542617414047626892980279957386761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-26039681626151771693701564287172000000000000)
      constant := (681146803546231011356310949301737064616620721) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree108.table
  base := (8591053859663037881253627761603231213563/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-26115076308430542232404819586653250000000000)
      constant := (685006941792011928205969233904632293277981215) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree108.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16140224243877755981/3125000000000000000)
  centralHi := (516487175804088191393/100000000000000000000)
  directionLo := (20755802179143136931/4000000000000000000)
  directionHi := (129723763619644605819/25000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree109.table
  base := (889821614110801621770808526209053154569/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-13140472304721918708775990622756000000000000)
      constant := (347046479321185685000109866230045704719985225) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree109.table
  base := (44491080494077613165124663694523151333923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-26357037390632596572354340760729187500000000)
      constant := (698024935017519391739474502009551363002639953) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree109.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20755802179143136931/4000000000000000000)
  centralHi := (129723763619644605819/25000000000000000000)
  directionLo := (130322952783309298451/25000000000000000000)
  directionHi := (104258362226647438761/20000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree110.table
  base := (46049976883518017703416029090458722252501/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-26522207592735903141402398203852000000000000)
      constant := (707161729894716606829521125459575598733152861) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree110.table
  base := (46049976700495656901489374342527861393309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (763999447091541458859653701410000000000000)
      linear := (-79796995418503952736911585804415375000000000)
      constant := (2133498620133989155026893603314785691467078647) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree110.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130322952783309298451/25000000000000000000)
  centralHi := (104258362226647438761/20000000000000000000)
  directionLo := (130919399619292099307/25000000000000000000)
  directionHi := (523677598477168397229/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree111.table
  base := (23815979031942865695264292246027511149397/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-13381735288013984432626407581096000000000000)
      constant := (360176558649347239525546180562596931524932317) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree111.table
  base := (47631957905491059471640985265135692212611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-26840959555036705252253383108881062500000000)
      constant := (724430756869082655741555947129994947291096321) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree111.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (130919399619292099307/25000000000000000000)
  centralHi := (523677598477168397229/100000000000000000000)
  directionLo := (105210513151311674751/20000000000000000000)
  directionHi := (131513141439139593439/25000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree112.table
  base := (49237024235913310161884050216812624726333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-27004733559320034589103232120532000000000000)
      constant := (733667120850431488437267590187213357526206213) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree112.table
  base := (49237024098843090855912617634845130989781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-27082920637238759592202904282957000000000000)
      constant := (737818585487088520400148996828022467287310941) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree112.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105210513151311674751/20000000000000000000)
  centralHi := (131513141439139593439/25000000000000000000)
  directionLo := (13210421471590666547/2500000000000000000)
  directionHi := (528416858863626661881/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree113.table
  base := (50865175390526999992367580245133472914899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-27245996542612100312953649078872000000000000)
      constant := (747103740546652009784980353232559183722278539) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree113.table
  base := (50865175271919453795456593451672663317761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (763999447091541458859653701410000000000000)
      linear := (-81974645158322441796457276371098812500000000)
      constant := (2253989077686693159022899015323051225330166413) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree113.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13210421471590666547/2500000000000000000)
  centralHi := (528416858863626661881/100000000000000000000)
  directionLo := (132692655110302192823/25000000000000000000)
  directionHi := (530770620441208771293/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree114.table
  base := (13129102880017424026225288965851890253893/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (78)
      previous := (39)
      next := (39)
      square := (352723659783721818494761635000000000000)
      linear := (-38070996573274468195019482046000000000000)
      constant := (1053549828787523307852777680755703780507786) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree114.table
  base := (2625820570872287051414653605067813984791/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (78)
      previous := (39)
      next := (39)
      square := (352723659783721818494761635000000000000)
      linear := (-38181222716956881263299095056937500000000)
      constant := (1059507033368260654490904777710845132035410) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree114.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132692655110302192823/25000000000000000000)
  centralHi := (530770620441208771293/100000000000000000000)
  directionLo := (133278497495795780393/25000000000000000000)
  directionHi := (533113989983183121573/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree115.table
  base := (3386920788630978740288194387985655309131/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-13864261254598115880327241497776000000000000)
      constant := (387172414180962016118516796634267572532770328) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree115.table
  base := (27095366264653968724031229270109866600403/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-13904401941922461306025733902592406250000000)
      constant := (389360871036920389775576958107947336403292358) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree115.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (133278497495795780393/25000000000000000000)
  centralHi := (533113989983183121573/100000000000000000000)
  directionLo := (107089420786188444301/20000000000000000000)
  directionHi := (267723551965471110753/50000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree116.table
  base := (27944069339597291649438341343266257280051/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-13984892746244148742252449976946000000000000)
      constant := (394074648238347750265254290973855118878098411) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree116.table
  base := (11177627720476648773330140384544638310387/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (763999447091541458859653701410000000000000)
      linear := (-84152294898140930856002966937782250000000000)
      constant := (2377808053518754450580657498635311974263245605) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree116.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107089420786188444301/20000000000000000000)
  centralHi := (267723551965471110753/50000000000000000000)
  directionLo := (53777009576609687893/10000000000000000000)
  directionHi := (537770095766096878931/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree117.table
  base := (14402157424710204680158494406866304234333/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-14105524237890181604177658456116000000000000)
      constant := (401038190363636237156720192602734471657188426) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree117.table
  base := (28804314816197586940865231621006512032161/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-14146363024124515645975255076668343750000000)
      constant := (403303452693786246439194415056691990247906996) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree117.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53777009576609687893/10000000000000000000)
  centralHi := (537770095766096878931/100000000000000000000)
  directionLo := (540083096099591674327/100000000000000000000)
  directionHi := (67510387012448959291/12500000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree118.table
  base := (59352205673264185684540603839776593908711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-28452311459072428932205733870572000000000000)
      constant := (816126081112293918452280399821935350401044671) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree118.table
  base := (14838051403947363432414584108991692893201/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-14267343565225542815950015663706312500000000)
      constant := (410367202358260357388493819166154216136078622) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree118.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (540083096099591674327/100000000000000000000)
  centralHi := (67510387012448959291/12500000000000000000)
  directionLo := (271193116378700024949/50000000000000000000)
  directionHi := (542386232757400049899/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree119.table
  base := (61118866599339279872025632618943414893971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-28693574442364494656056150828912000000000000)
      constant := (830298397630631561988024520534776572776723531) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree119.table
  base := (61118866549627750735361812028942384643409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (763999447091541458859653701410000000000000)
      linear := (-86329944637959419915548657504465687500000000)
      constant := (2504955547476106233380943244843511700713343197) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree119.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271193116378700024949/50000000000000000000)
  centralHi := (542386232757400049899/100000000000000000000)
  directionLo := (54467963086295811127/10000000000000000000)
  directionHi := (544679630862958111271/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree120.table
  base := (62908612474490645548156221720766190434257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-28934837425656560379906567787252000000000000)
      constant := (844593330281355665400361991293836594746766777) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree120.table
  base := (62908612431496680871575382815789442819419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-29018609294855194311799073675564500000000000)
      constant := (849359238713245350294526311858911082607810259) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree120.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54467963086295811127/10000000000000000000)
  centralHi := (544679630862958111271/100000000000000000000)
  directionLo := (546963412916487566377/100000000000000000000)
  directionHi := (273481706458243783189/50000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree121.table
  base := (64721443296611549539036035634066346177027/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-29176100408948626103756984745592000000000000)
      constant := (859010879063705698013516234979579950969906747) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree121.table
  base := (64721443259429910136325207066727520693427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-29260570377057248651748594849640437500000000)
      constant := (863856573379440685704910772201079245810170897) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree121.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (546963412916487566377/100000000000000000000)
  centralHi := (273481706458243783189/50000000000000000000)
  directionLo := (109847539774270018901/20000000000000000000)
  directionHi := (274618849435675047253/50000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree122.table
  base := (16639339765998604185138045172025060771037/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-14708681696120345913803700851966000000000000)
      constant := (436775521988532612607451248488434093876688714) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree122.table
  base := (8319669878980184578395613327132041379197/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (381999723545770729429826850705000000000000)
      linear := (-44253797188888954487547174035574562500000000)
      constant := (1317715779735073327667026980185327379231243904) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree122.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109847539774270018901/20000000000000000000)
  centralHi := (274618849435675047253/50000000000000000000)
  directionLo := (551502606207567809883/100000000000000000000)
  directionHi := (137875651551891952471/25000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree123.table
  base := (68416359775271263515797977903063059763567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-29658626375532757551457818662272000000000000)
      constant := (888213825020940404911597466173991764574647687) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree123.table
  base := (6841635974746872776916185314891170792841/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-14872246270730678665823818598896156250000000)
      constant := (446610539022307065467148638401789569872874880) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree123.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (551502606207567809883/100000000000000000000)
  centralHi := (137875651551891952471/25000000000000000000)
  directionLo := (69219781250329665461/12500000000000000000)
  directionHi := (553758250002637323689/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree124.table
  base := (35149222714681351154736435974949145635363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-14949944679412411637654117810306000000000000)
      constant := (451499611097470789098068821048580641574366043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree124.table
  base := (70298445405323496513252665393861597239669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-29986453623663411671597158371868250000000000)
      constant := (908088248042779694869036761603257935041020509) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree124.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69219781250329665461/12500000000000000000)
  centralHi := (553758250002637323689/100000000000000000000)
  directionLo := (11120094859995163671/2000000000000000000)
  directionHi := (556004742999758183551/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree125.table
  base := (2256363000794821688449624935791401042667/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-15070576171058444499579326289476000000000000)
      constant := (458953617749383756278301922261756132422444592) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree125.table
  base := (4512726000290646057703930543603318473203/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (381999723545770729429826850705000000000000)
      linear := (-45342622058798199017320019318916281250000000)
      constant := (1384618044726409291398916194588604010870971417) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree125.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11120094859995163671/2000000000000000000)
  centralHi := (556004742999758183551/100000000000000000000)
  directionLo := (279121097836795075421/50000000000000000000)
  directionHi := (558242195673590150843/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree126.table
  base := (37065935781429599517880818018474306670693/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-15191207662704477361504534768646000000000000)
      constant := (466468932466095959440975936293165224708120173) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree126.table
  base := (74131871544890808093721211253559404919553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-30470375788067520351496200720020125000000000)
      constant := (938192423368892031958144237608784982285333633) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree126.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (279121097836795075421/50000000000000000000)
  centralHi := (558242195673590150843/100000000000000000000)
  directionLo := (560470716293647835611/100000000000000000000)
  directionHi := (140117679073411958903/25000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree127.table
  base := (76083212041186227015747323465144156375137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-30623678308701020446859486495632000000000000)
      constant := (948091110495051917470327153229391040451424457) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree127.table
  base := (76083212025652939797622552472102018822309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-30712336870269574691445721894096062500000000)
      constant := (953429428696495706693688251159603119322197299) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree127.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (560470716293647835611/100000000000000000000)
  centralHi := (140117679073411958903/25000000000000000000)
  directionLo := (562690410985435621501/100000000000000000000)
  directionHi := (281345205492717810751/50000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree128.table
  base := (78057637460112514258475477878074184063099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-30864941291993086170709903453972000000000000)
      constant := (963366972187238174521744767223680780446778739) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree128.table
  base := (152456323138056908381259100835341276569/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (381999723545770729429826850705000000000000)
      linear := (-46431446928707443547092864602258000000000000)
      constant := (1453184568700489589046816995716380698246202112) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree128.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (562690410985435621501/100000000000000000000)
  centralHi := (281345205492717810751/50000000000000000000)
  directionLo := (282450691894710277441/50000000000000000000)
  directionHi := (564901383789420554883/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree129.table
  base := (40027573909730083352957744531762990512509/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-15553102137642575947280160206156000000000000)
      constant := (489382725004343235140627832141295439575015749) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree129.table
  base := (80055147807853887247989337601072396890269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-31196259034673683371344764242247937500000000)
      constant := (984273274680335891876454847124682300804730859) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree129.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282450691894710277441/50000000000000000000)
  centralHi := (564901383789420554883/100000000000000000000)
  directionLo := (141775934179483980437/25000000000000000000)
  directionHi := (567103736717935921749/100000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree130.table
  base := (2051893577978907537206859826528031681177/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-15673733629288608809205368685326000000000000)
      constant := (497143271979685247016432292208212388738097940) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree130.table
  base := (16415148621824944676431750444940519925541/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-31438220116875737711294285416323875000000000)
      constant := (999880115336511761683638562966409425574976505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree130.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141775934179483980437/25000000000000000000)
  centralHi := (567103736717935921749/100000000000000000000)
  directionLo := (569297569810103572597/100000000000000000000)
  directionHi := (284648784905051786299/50000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree131.table
  base := (84119423359216000478315904145043416659689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-31588730241869283342261154328992000000000000)
      constant := (1009930254039295690332639228478162673414147729) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree131.table
  base := (5257463959409123569770261660664630443829/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (381999723545770729429826850705000000000000)
      linear := (-47520271798616688076865709885599718750000000)
      constant := (1523415351653307174752787726787667155284475081) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree131.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (569297569810103572597/100000000000000000000)
  centralHi := (284648784905051786299/50000000000000000000)
  directionLo := (571482981184858660709/100000000000000000000)
  directionHi := (57148298118485866071/10000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree132.table
  base := (86186188539727758748266318179095823689187/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-31829993225161349066111571287332000000000000)
      constant := (1025696580248494005901653289274637592351796507) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree132.table
  base := (21546547133058729876550940022970798388917/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-15961071140639923195596663882237875000000000)
      constant := (515731815988728645591114426461663615655548074) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree132.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (571482981184858660709/100000000000000000000)
  centralHi := (57148298118485866071/10000000000000000000)
  directionLo := (573660067092156315553/100000000000000000000)
  directionHi := (286830033546078157777/50000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree133.table
  base := (44138019330420535139986745423946448271493/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (78)
      previous := (39)
      next := (39)
      square := (352723659783721818494761635000000000000)
      linear := (-44420022449381460927925191476000000000000)
      constant := (1442639227959860675993564879096946448271493) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree133.table
  base := (1103450483179574334311729624436401312157/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (78)
      previous := (39)
      next := (39)
      square := (352723659783721818494761635000000000000)
      linear := (-44548619617010942840918073322093750000000)
      constant := (1450748348978299505194561678723198972408155) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree133.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (573660067092156315553/100000000000000000000)
  centralHi := (286830033546078157777/50000000000000000000)
  directionLo := (14395723049060896611/2500000000000000000)
  directionHi := (575828921962435864441/100000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree134.table
  base := (5649310857672240267459637944974765985107/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-16156259595872740256906202602006000000000000)
      constant := (528798540527472032026538424075871124164989016) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree134.table
  base := (18077794743432103259176228897660507441087/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (763999447091541458859653701410000000000000)
      linear := (-97218193337051865213277110337882875000000000)
      constant := (3190620787170728752052589003588590149746611105) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree134.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14395723049060896611/2500000000000000000)
  centralHi := (575828921962435864441/100000000000000000000)
  directionLo := (288994819227207263419/50000000000000000000)
  directionHi := (577989638454414526839/100000000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree135.table
  base := (46262496862856694592188121647764096249557/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-16276891087518773118831411081176000000000000)
      constant := (536865627826177543102464336425327838746090077) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree135.table
  base := (92524993720878581213155030999840305461341/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-32648025527886009411041891286703562500000000)
      constant := (1079763495261283158035935644375579086111387851) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree135.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (288994819227207263419/50000000000000000000)
  centralHi := (577989638454414526839/100000000000000000000)
  directionLo := (580142307501279023257/100000000000000000000)
  directionHi := (290071153750639511629/50000000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree136.table
  base := (47342049334994369482845027114297509314669/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-16397522579164805980756619560346000000000000)
      constant := (544994023189675880893157065503317400862595509) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree136.table
  base := (94684098665811306505684378745540969824561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-32889986610088063750991412460779500000000000)
      constant := (1096110006575558075373913151657718383856666521) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree136.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (580142307501279023257/100000000000000000000)
  centralHi := (290071153750639511629/50000000000000000000)
  directionLo := (291143509177670125579/50000000000000000000)
  directionHi := (582287018355340251159/100000000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree137.table
  base := (48433144277942064243583617597589114712647/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-16518154070810838842681828039516000000000000)
      constant := (553183726618021598791545434257226670411265567) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree137.table
  base := (96866288552274882341347827461375221093673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (763999447091541458859653701410000000000000)
      linear := (-99395843076870354272822800904566312500000000)
      constant := (3337739388999545442046199135961900087588979109) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree137.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291143509177670125579/50000000000000000000)
  centralHi := (582287018355340251159/100000000000000000000)
  directionLo := (584423858631213071973/100000000000000000000)
  directionHi := (292211929315606535987/50000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree138.table
  base := (49535781691861726140201552543348601633289/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-16638785562456871704607036518686000000000000)
      constant := (561434738111273159760582397746956845189617329) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree138.table
  base := (19814312676121055081872051883452075128649/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-33373908774492172430890454808931375000000000)
      constant := (1129172864534275657935201897863764173341586445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree138.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (584423858631213071973/100000000000000000000)
  centralHi := (292211929315606535987/50000000000000000000)
  directionLo := (586552914347580314873/100000000000000000000)
  directionHi := (293276457173790157437/50000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree139.table
  base := (50649961576923782372416206094860930078319/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-16759417054102904566532244997856000000000000)
      constant := (569747057669492088019365928038233795758273159) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree139.table
  base := (50649961575576891245940907937106140690011/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-16807934928347113385419987991503656250000000)
      constant := (572944605589483212635839760141168768693390846) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree139.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (586552914347580314873/100000000000000000000)
  centralHi := (293276457173790157437/50000000000000000000)
  directionLo := (588674269967597323821/100000000000000000000)
  directionHi := (294337134983798661911/50000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree140.table
  base := (103551367866610300072789658865058534308657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-33760097091497874856914906954052000000000000)
      constant := (1156241370585484501279224805614366130885425177) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree140.table
  base := (51775683932141634890506181309413447778331/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (381999723545770729429826850705000000000000)
      linear := (-50786746408344421666184245735624875000000000)
      constant := (1744093254401077666080270946187971892850182473) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree140.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (588674269967597323821/100000000000000000000)
  centralHi := (294337134983798661911/50000000000000000000)
  directionLo := (147697002109497686273/25000000000000000000)
  directionHi := (590788008437990745093/100000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree141.table
  base := (52912948761187553798152052026291663675791/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-17000680037394970290382661956196000000000000)
      constant := (586555620981089250225753103292452290586960551) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree141.table
  base := (105825897520364998178393139152706535004033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-34099792021098335450739018331159187500000000)
      constant := (1179691739799665739466197716852773783257549663) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree141.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (147697002109497686273/25000000000000000000)
  centralHi := (590788008437990745093/100000000000000000000)
  directionLo := (592894211226902763673/100000000000000000000)
  directionHi := (296447105613451381837/50000000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree142.table
  base := (13515439015189026646382750657113197520151/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-17121311529041003152307870435366000000000000)
      constant := (595051864734599912544739398973623457219098044) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree142.table
  base := (108123512119775949129054422260676020071963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-34341753103300389790688539505235125000000000)
      constant := (1196777921775944401811386708384036861605353643) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree142.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (592894211226902763673/100000000000000000000)
  centralHi := (296447105613451381837/50000000000000000000)
  directionLo := (594992958360529640351/100000000000000000000)
  directionHi := (18593529948766551261/3125000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree143.table
  base := (55222105832198115002823196508317582969627/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-17241943020687036014233078914536000000000000)
      constant := (603609416553341855280720526862915647452035347) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree143.table
  base := (110444211662896577809636958831401792387093/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (763999447091541458859653701410000000000000)
      linear := (-103751142556507332391914182037933187500000000)
      constant := (3641962146589075326223544745037737247112252969) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree143.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (594992958360529640351/100000000000000000000)
  centralHi := (18593529948766551261/3125000000000000000)
  directionLo := (298542164229300584469/50000000000000000000)
  directionHi := (597084328458601168939/100000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree144.table
  base := (2255759923028083066270183330861951631333/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-17362574512333068876158287393706000000000000)
      constant := (612228276437383126069724554767973113472780325) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree144.table
  base := (11278799615010893100576131050349292404353/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-17412837633852249235293790926693500000000000)
      constant := (615660060530522889572595679744969160289857165) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree144.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (298542164229300584469/50000000000000000000)
  centralHi := (597084328458601168939/100000000000000000000)
  directionLo := (599168398768745557641/100000000000000000000)
  directionHi := (299584199384372778821/50000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree145.table
  base := (115154865582913682570702211558603472063193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-34966412007958203476166991745752000000000000)
      constant := (1241816888773583799334357696123345853414812673) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree145.table
  base := (57577432790897538012259501576038789220001/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-17533818174953276405268551513731468750000000)
      constant := (624388069185072169660638041328517921609592236) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree145.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (599168398768745557641/100000000000000000000)
  centralHi := (299584199384372778821/50000000000000000000)
  directionLo := (300622622599891116539/50000000000000000000)
  directionHi := (601245245199782233079/100000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree146.table
  base := (117544819959301823226814392770156987198367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-35207674991250269200017408704092000000000000)
      constant := (1259299840803272451113468393647258672378610487) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree146.table
  base := (117544819958335794710470093123164729165097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (763999447091541458859653701410000000000000)
      linear := (-105928792296325821451459872604616625000000000)
      constant := (3799066302371374754545965794564342669263925051) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree146.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (300622622599891116539/50000000000000000000)
  centralHi := (601245245199782233079/100000000000000000000)
  directionLo := (18853591948561973861/3125000000000000000)
  directionHi := (603314942353983163553/100000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree147.table
  base := (59978929640471863315384153673940537672867/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-17724468987271167461933912831216000000000000)
      constant := (638452704481983818556871129843049534099904987) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree147.table
  base := (119957859280109503251173966677751609776979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-35551558514310661490436145375614812500000000)
      constant := (1284058008322124123971037844523393461500583169) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree147.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18853591948561973861/3125000000000000000)
  centralHi := (603314942353983163553/100000000000000000000)
  directionLo := (30268878177917074691/5000000000000000000)
  directionHi := (605377563558341493821/100000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree148.table
  base := (122393983548211732860890644217084567743449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-35690200957834400647718242620772000000000000)
      constant := (1294633593255803772103455228941903528955385089) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree148.table
  base := (122393983547491364128910645854732403471051/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-35793519596512715830385666549690750000000000)
      constant := (1301883860965277390344526909618914358590549411) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree148.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30268878177917074691/5000000000000000000)
  centralHi := (605377563558341493821/100000000000000000000)
  directionLo := (607433180894884571111/100000000000000000000)
  directionHi := (75929147611860571389/12500000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree149.table
  base := (6242659638073729311522154775219243247179/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-17965731970563233185784329789556000000000000)
      constant := (656242196839456986389847386136190468122316190) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree149.table
  base := (124853192760852561434109758647157940696039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (763999447091541458859653701410000000000000)
      linear := (-108106442036144310511005563171300062500000000)
      constant := (3959498976160156144277302667540504792449591487) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree149.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (607433180894884571111/100000000000000000000)
  centralHi := (75929147611860571389/12500000000000000000)
  directionLo := (609481865230066816333/100000000000000000000)
  directionHi := (304740932615033408167/50000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree150.table
  base := (63667743460548398798029193848203442677579/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-18086363462209266047709538268726000000000000)
      constant := (665228905116714913780852651969601442806606019) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree150.table
  base := (127335486920559714919032955555943880346579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-36277441760916824510284708897842625000000000)
      constant := (1337905401586580446945326239037985731039490019) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree150.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (609481865230066816333/100000000000000000000)
  centralHi := (304740932615033408167/50000000000000000000)
  directionLo := (611523686243276350291/100000000000000000000)
  directionHi := (152880921560819087573/25000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree151.table
  base := (64920433013719065665297578033435713193579/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-18206994953855298909634746747896000000000000)
      constant := (674276921459740605694044395638091292462882019) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree151.table
  base := (64920433013487205868422491351145549007269/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-18259701421559439425117115035959281250000000)
      constant := (678050544782496559932747716271060137674045984) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree151.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (611523686243276350291/100000000000000000000)
  centralHi := (152880921560819087573/25000000000000000000)
  directionLo := (61355871245448781767/10000000000000000000)
  directionHi := (613558712454487817671/100000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree152.table
  base := (132369330080853198022428260780966549109901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (156)
      previous := (78)
      next := (78)
      square := (705447319567443636989523270000000000000)
      linear := (-101538096650976907321661801812000000000000)
      constant := (3786073384313562711028389359564966549109901) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree152.table
  base := (132369330080452837866565008126399150624623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 30000000000000000000000000000000000000000
      center := (468)
      previous := (234)
      next := (234)
      square := (2116341958702330910968569810000000000000)
      linear := (-305496099102390026511222309523500000000000)
      constant := (11421773318466082963917183291039478701873869) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree152.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61355871245448781767/10000000000000000000)
  centralHi := (613558712454487817671/100000000000000000000)
  directionLo := (307793505625546228637/50000000000000000000)
  directionHi := (24623480450043698291/4000000000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree153.table
  base := (13492087908169113670613761225885230012943/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-18448257937147364633485163706236000000000000)
      constant := (692556878343350324316333977090595840173362115) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree153.table
  base := (3373021977033637346038947080285785229603/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-18501662503761493765066636210035218750000000)
      constant := (696431150428991784007743910413099346652655535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree153.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307793505625546228637/50000000000000000000)
  centralHi := (24623480450043698291/4000000000000000000)
  directionLo := (617608648913935141381/100000000000000000000)
  directionHi := (308804324456967570691/50000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree154.table
  base := (13749551303029537278014092004303458500453/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-18568889428793397495410372185406000000000000)
      constant := (701788818884059358905587885277871742593317665) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree154.table
  base := (137495513029996981640823678439808185097487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-37245286089725041870082793594146375000000000)
      constant := (1411427824172812275252274752399618276304567807) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree154.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (617608648913935141381/100000000000000000000)
  centralHi := (308804324456967570691/50000000000000000000)
  directionLo := (309811845321293423187/50000000000000000000)
  directionHi := (4956989525140694771/800000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree155.table
  base := (7004661596350171989047381256339930618807/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-18689520920439430357335580664576000000000000)
      constant := (711082067490786097911725958062592149533893270) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree155.table
  base := (140093231926745851522053540900513382837421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (763999447091541458859653701410000000000000)
      linear := (-112461741515781288630096944304666937500000000)
      constant := (4290349877800080965034265064523397626913708193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree155.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (309811845321293423187/50000000000000000000)
  centralHi := (4956989525140694771/800000000000000000)
  directionLo := (621632200579879817343/100000000000000000000)
  directionHi := (4856501567030311073/781250000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree156.table
  base := (71357017886073427454674091265521283666267/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-18810152412085463219260789143746000000000000)
      constant := (720436624163590380189490872576029183403522387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree156.table
  base := (142714035771924499219258624948775891855033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-37729208254129150549981835942298250000000000)
      constant := (1448928706139747702152906654872979120397166913) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree156.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (621632200579879817343/100000000000000000000)
  centralHi := (4856501567030311073/781250000000000000)
  directionLo := (623634241835731547919/100000000000000000000)
  directionHi := (7795428022946644349/1250000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree157.table
  base := (145357924566051039682124230171716153644179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-37861567807462992162371995245832000000000000)
      constant := (1459704977805061888645323428924023531465548619) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree157.table
  base := (72678962282929552667597479976059484164161/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-18985584668165602444965678558187093750000000)
      constant := (733932032396046083937162289548416953031308996) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree157.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (623634241835731547919/100000000000000000000)
  centralHi := (7795428022946644349/1250000000000000000)
  directionLo := (156407469127570652469/25000000000000000000)
  directionHi := (625629876510282609877/100000000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree158.table
  base := (148024898309035278349045951613293512996897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-38102830790755057886222412204172000000000000)
      constant := (1478659323415330842236644003707854958191879817) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree158.table
  base := (148024898308869609963617411108766901911789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (763999447091541458859653701410000000000000)
      linear := (-114639391255599777689642634871350375000000000)
      constant := (4460768105671527651648562901547767603598592487) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree158.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156407469127570652469/25000000000000000000)
  centralHi := (625629876510282609877/100000000000000000000)
  directionLo := (627619165716372332211/100000000000000000000)
  directionHi := (156904791429093083053/25000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree159.table
  base := (2354921203147073559363532058566377254427/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-19172046887023561805036414581256000000000000)
      constant := (748868142579050331784963797984867790043140704) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree159.table
  base := (18839369625158714575948570882534722302019/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-19227545750367656784915199732263031250000000)
      constant := (753052308717556048571550706814923737392787311) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree159.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (627619165716372332211/100000000000000000000)
  centralHi := (156904791429093083053/25000000000000000000)
  directionLo := (19675067800042979487/3125000000000000000)
  directionHi := (125920433920275068717/20000000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree160.table
  base := (153428100643490333609671269397915862948617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-38585356757339189333923246120852000000000000)
      constant := (1516935863033482181658430318424167626524450737) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree160.table
  base := (153428100643366920342492680348289513918447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-38697052582937367909779920638602000000000000)
      constant := (1525409811426011813377279633606140014524559367) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree160.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19675067800042979487/3125000000000000000)
  centralHi := (125920433920275068717/20000000000000000000)
  directionLo := (631578947368421052631/100000000000000000000)
  directionHi := (78947368421052631579/12500000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree161.table
  base := (156164329235569067682563708948369831081181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-38826619740631255057773663079192000000000000)
      constant := (1536258057041584025698883230754523509020306341) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree161.table
  base := (156164329235462555927361054627253466844049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (763999447091541458859653701410000000000000)
      linear := (-116817040995418266749188325438033812500000000)
      constant := (4634514851589951443300197783192171282424136317) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree161.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (631578947368421052631/100000000000000000000)
  centralHi := (78947368421052631579/12500000000000000000)
  directionLo := (633549557297017245257/100000000000000000000)
  directionHi := (316774778648508622629/50000000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree162.table
  base := (158923642777943783600298449175057796700123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-39067882723923320781624080037532000000000000)
      constant := (1555702867182512645054516516398739864608744403) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree162.table
  base := (158923642777851862213861840703788803951537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-39180974747341476589678962986753875000000000)
      constant := (1564390034747134681536912498444788232835879857) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree162.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (633549557297017245257/100000000000000000000)
  centralHi := (316774778648508622629/50000000000000000000)
  directionLo := (317757028381549062121/50000000000000000000)
  directionHi := (635514056763098124243/100000000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree163.table
  base := (80853020635451693203282968290605073854781/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-19654572853607693252737248497936000000000000)
      constant := (787635146728186167223051213272241431661575941) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree163.table
  base := (1293648330166592478035953694700729678537/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-39422935829543530929628484160829812500000000)
      constant := (1584065064077568823307271547295083572740075875) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree163.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (317757028381549062121/50000000000000000000)
  centralHi := (635514056763098124243/100000000000000000000)
  directionLo := (63747250225851630221/10000000000000000000)
  directionHi := (637472502258516302211/100000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree164.table
  base := (32902304942946178804382319340233074470337/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-39550408690507452229324913954212000000000000)
      constant := (1594960335863265263342957859809648699418958285) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree164.table
  base := (164511524714662438983568618843340900889423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10830000000000000000000000000000000000000000
      center := (168948)
      previous := (84474)
      next := (84474)
      square := (763999447091541458859653701410000000000000)
      linear := (-118994690735236755808734016004717250000000000)
      constant := (4811590115564165522773787441077128015975745109) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree164.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63747250225851630221/10000000000000000000)
  centralHi := (637472502258516302211/100000000000000000000)
  directionLo := (319712474704998741051/50000000000000000000)
  directionHi := (639424949409997482103/100000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree165.table
  base := (83670046554851763963432798111263739899643/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-19895835836899758976587665456276000000000000)
      constant := (807386497201645754349777103184231210103771123) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree165.table
  base := (167340093109644456747948827043538427236327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-39906857993947639609527526508981687500000000)
      constant := (1623784958078693896310603116918088229165907797) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree165.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319712474704998741051/50000000000000000000)
  centralHi := (639424949409997482103/100000000000000000000)
  directionLo := (641371452997575817931/100000000000000000000)
  directionHi := (160342863249393954483/25000000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree166.table
  base := (170191746456092811110032532883522944958473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-40032934657091583677025747870892000000000000)
      constant := (1634708269076549090314777726004423783130008753) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree166.table
  base := (34038349291208367861826391346599158954203/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-40148819076149693949477047683057625000000000)
      constant := (1643829822749583082645693917398647378396711415) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree166.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (641371452997575817931/100000000000000000000)
  centralHi := (160342863249393954483/25000000000000000000)
  directionLo := (32165603348626362039/5000000000000000000)
  directionHi := (643312066972527240781/100000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree167.table
  base := (4326662118854116789737828988313800254549/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-20137098820191824700438082414616000000000000)
      constant := (827383079941567004101581395247902637837843780) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree167.table
  base := (4326662118853017255812387906699141202033/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5415000000000000000000000000000000000000000
      center := (84474)
      previous := (42237)
      next := (42237)
      square := (381999723545770729429826850705000000000000)
      linear := (-60586170237527622434139853285700343750000000)
      constant := (2495996948801228194975454243475990986570800405) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree167.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32165603348626362039/5000000000000000000)
  centralHi := (643312066972527240781/100000000000000000000)
  directionLo := (645246844474817359237/100000000000000000000)
  directionHi := (322623422237408679619/50000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree168.table
  base := (43991077001044887520421374320239335755923/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-20257730311837857562363290893786000000000000)
      constant := (837473333411570140731660932731900800415776406) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree168.table
  base := (87982154002070800915341658394163704910757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1805000000000000000000000000000000000000000
      center := (28158)
      previous := (14079)
      next := (14079)
      square := (127333241181923576476608950235000000000000)
      linear := (-20316370620276901314688045015604750000000000)
      constant := (842144693716247556074647133747812269347783277) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree168.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell034.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (645246844474817359237/100000000000000000000)
  centralHi := (322623422237408679619/50000000000000000000)
  directionLo := (647175837850079897887/100000000000000000000)
  directionHi := (20224244932814996809/3125000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 9
  qDenominator := 19
  table := BinomialMassData.Q9_19.Degree169.table
  base := (178885216206392510618166746516714360629039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-40756723606967780848576998745912000000000000)
      constant := (1695249789896659988210668760248471884187083079) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_19.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 1733
  qDenominator := 3648
  table := BinomialMassData.Q1733_3648.Degree169.table
  base := (178885216206359769042338227476048403498589/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3610000000000000000000000000000000000000000
      center := (56316)
      previous := (28158)
      next := (28158)
      square := (254666482363847152953217900470000000000000)
      linear := (-40874702322755856969325611205285437500000000)
      constant := (1704704087444704154515518308708229225127834379) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1733_3648.Degree169.checked
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
end ForestUnimodality.Stage130KernelData.Cell034.Kernel169
