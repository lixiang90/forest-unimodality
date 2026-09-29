import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell020.Parameters
import ForestUnimodality.BinomialMassData.Q103_255.Batch000_049
import ForestUnimodality.BinomialMassData.Q103_255.Batch050_099
import ForestUnimodality.BinomialMassData.Q103_255.Batch100_149
import ForestUnimodality.BinomialMassData.Q7_17.Batch000_049
import ForestUnimodality.BinomialMassData.Q7_17.Batch050_099
import ForestUnimodality.BinomialMassData.Q7_17.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree000.table
  base := (16308884077244107869688604871/1000000000000000000000000000)
  polynomial :=
    { denominator := 63750000000000000000000000000000000000000
      center := (152)
      previous := (103)
      next := (0)
      square := (2391370084823671408880141355000000000000)
      linear := (7917907487879530109564640562500000000000)
      constant := (1039691359924311876692648560526250000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree000.table
  base := (16308884077244107869688604871/1000000000000000000000000000)
  polynomial :=
    { denominator := 4250000000000000000000000000000000000000
      center := (10)
      previous := (7)
      next := (0)
      square := (159424672321578093925342757000000000000)
      linear := (527860499191968673970976037500000000000)
      constant := (69312757328287458446176570701750000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree001.table
  base := (104004578118054955013786305139065167243367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (62016)
      previous := (42024)
      next := (0)
      square := (975678994608057934823097672840000000000000)
      linear := (2442310675096966188335478758892000000000000)
      constant := (269370221128579297028656417378150899999997567) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree001.table
  base := (51432329686406211856926488227179642445213/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (3400)
      previous := (2380)
      next := (0)
      square := (54204388589336551934616537380000000000000)
      linear := (134833661475227482851035880790000000000000)
      constant := (14799233172947763525945632328984916666666557) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (24534105599399297661/50000000000000000000)
  directionHi := (49068211198798595323/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree002.table
  base := (528015525513189756044218442243350153787/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 3251250000000000000000000000000000000000000
      center := (7752)
      previous := (5253)
      next := (0)
      square := (121959874326007241852887209105000000000000)
      linear := (206764386892385511496073021035500000000000)
      constant := (21727268620016721046949376739295459999999792) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree002.table
  base := (66195151543490518198402777397495670895809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (6800)
      previous := (4760)
      next := (0)
      square := (108408777178673103869233074760000000000000)
      linear := (180389506450371233103879817660000000000000)
      constant := (18908319824227208611113167099516248888888801) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24534105599399297661/50000000000000000000)
  centralHi := (49068211198798595323/100000000000000000000)
  directionLo := (69392929758728358263/100000000000000000000)
  directionHi := (8674116219841044783/12500000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree003.table
  base := (11224157152199451963372060747429447075413/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2167500000000000000000000000000000000000000
      center := (5168)
      previous := (3502)
      next := (0)
      square := (81306582884004827901924806070000000000000)
      linear := (72159959598433499633474131473000000000000)
      constant := (9524514910596967411620381333953130614383071) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree003.table
  base := (43611224096227923281361263707526865704461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (6800)
      previous := (4760)
      next := (0)
      square := (108408777178673103869233074760000000000000)
      linear := (91111689950287500505687873740000000000000)
      constant := (12325667486827006587874435118415264188589229) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69392929758728358263/100000000000000000000)
  centralHi := (8674116219841044783/12500000000000000000)
  directionLo := (21247158708209833911/25000000000000000000)
  directionHi := (16997726966567867129/20000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree004.table
  base := (15268516144776448888128774137917564459087/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (31008)
      previous := (21012)
      next := (0)
      square := (487839497304028967411548836420000000000000)
      linear := (38861967611659949617397493534000000000000)
      constant := (38377144964725695232746359812462785158085287) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree004.table
  base := (29466583192157196379814217543095690695003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (6800)
      previous := (4760)
      next := (0)
      square := (108408777178673103869233074760000000000000)
      linear := (1833873450203767907495929820000000000000)
      constant := (8218730414262230075712859758514654610855867) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21247158708209833911/25000000000000000000)
  centralHi := (16997726966567867129/20000000000000000000)
  directionLo := (19627284479519438129/20000000000000000000)
  directionHi := (49068211198798595323/50000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree005.table
  base := (106225879094564986913758722418180665763/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3251250000000000000000000000000000000000000
      center := (7752)
      previous := (5253)
      next := (0)
      square := (121959874326007241852887209105000000000000)
      linear := (-88808955591820274641512450442500000000000)
      constant := (6589245184125326672327285685249697791239075) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree005.table
  base := (1019704154385781731030758837424307007901/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144500000000000000000000000000000000000000
      center := (340)
      previous := (238)
      next := (0)
      square := (5420438858933655193461653738000000000000)
      linear := (-4372197152493998234534800705000000000000)
      constant := (280720174332162897214455672840624725283389) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19627284479519438129/20000000000000000000)
  centralHi := (49068211198798595323/50000000000000000000)
  directionLo := (27429963943707526563/25000000000000000000)
  directionHi := (109719855774830106253/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree006.table
  base := (15064780555477465533589305510167467396443/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (20672)
      previous := (14008)
      next := (0)
      square := (325226331536019311607699224280000000000000)
      linear := (-499555741564148097832998064716000000000000)
      constant := (12361637603844736691763308061623994232716081) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree006.table
  base := (7199857067101393996267765241100074833659/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (3400)
      previous := (2380)
      next := (0)
      square := (54204388589336551934616537380000000000000)
      linear := (-88360879774981848644443979010000000000000)
      constant := (1968208957747830070179063840057921626927451) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27429963943707526563/25000000000000000000)
  centralHi := (109719855774830106253/100000000000000000000)
  directionLo := (24038416005635166059/20000000000000000000)
  directionHi := (15024010003521978787/12500000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree007.table
  base := (675824619902119444071780899209463565893/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3251250000000000000000000000000000000000000
      center := (7752)
      previous := (5253)
      next := (0)
      square := (121959874326007241852887209105000000000000)
      linear := (-285857850581290798733236098094500000000000)
      constant := (3348883072794143905370937234947329469775386) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree007.table
  base := (10293105352235830719135928194791553548119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (6800)
      previous := (4760)
      next := (0)
      square := (108408777178673103869233074760000000000000)
      linear := (-265999576050047429887079901940000000000000)
      constant := (2840756487777800014528930119634758975406391) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24038416005635166059/20000000000000000000)
  centralHi := (15024010003521978787/12500000000000000000)
  directionLo := (8113892756925975621/6250000000000000000)
  directionHi := (129822284110815609937/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree008.table
  base := (3886755413103030574215422269391365466437/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (31008)
      previous := (21012)
      next := (0)
      square := (487839497304028967411548836420000000000000)
      linear := (-1537529192304104243116391687682000000000000)
      constant := (9983873334139775470652997500443741578202637) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree008.table
  base := (7361483556771062177598709233867683562621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (6800)
      previous := (4760)
      next := (0)
      square := (108408777178673103869233074760000000000000)
      linear := (-355277392550131162485271845860000000000000)
      constant := (2121427753012048086807216846827760549597469) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8113892756925975621/6250000000000000000)
  centralHi := (129822284110815609937/100000000000000000000)
  directionLo := (138785859517456716527/100000000000000000000)
  directionHi := (8674116219841044783/6250000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree009.table
  base := (5509294141910210629582233840347163815597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (20672)
      previous := (14008)
      next := (0)
      square := (325226331536019311607699224280000000000000)
      linear := (-1287751321522030194199892655324000000000000)
      constant := (5159928692092964125750281301325791028122599) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree009.table
  base := (5176020598205145202734172186437003463337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (6800)
      previous := (4760)
      next := (0)
      square := (108408777178673103869233074760000000000000)
      linear := (-444555209050214895083463789780000000000000)
      constant := (1654500375963039916453164153340294000904393) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (138785859517456716527/100000000000000000000)
  centralHi := (8674116219841044783/6250000000000000000)
  directionLo := (9200289599774736623/6250000000000000000)
  directionHi := (147204633596395785969/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree010.table
  base := (3753199699609130036029902472096718823011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (62016)
      previous := (42024)
      next := (0)
      square := (975678994608057934823097672840000000000000)
      linear := (-4651449544523972678966572556580000000000000)
      constant := (12631820630748441588600296297163565658651611) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree010.table
  base := (1738463730471528825069128622562936896399/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (3400)
      previous := (2380)
      next := (0)
      square := (54204388589336551934616537380000000000000)
      linear := (-266916512775149313840827866850000000000000)
      constant := (682447665561907051866999377420688763059311) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9200289599774736623/6250000000000000000)
  centralHi := (147204633596395785969/100000000000000000000)
  directionLo := (38791827024596172363/25000000000000000000)
  directionHi := (155167308098384689453/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree011.table
  base := (468004884547244994919786023141793877433/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (62016)
      previous := (42024)
      next := (0)
      square := (975678994608057934823097672840000000000000)
      linear := (-5439645124481854775333467147188000000000000)
      constant := (10994157129538486558706384432489429376016165) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree011.table
  base := (1052633133573499643398421207475417154367/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (3400)
      previous := (2380)
      next := (0)
      square := (54204388589336551934616537380000000000000)
      linear := (-311555421025191180139923838810000000000000)
      constant := (603339785899623190654319697390395557612063) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38791827024596172363/25000000000000000000)
  centralHi := (155167308098384689453/100000000000000000000)
  directionLo := (162740845680329874321/100000000000000000000)
  directionHi := (81370422840164937161/50000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree012.table
  base := (1166440384276195097218761324193540746499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (20672)
      previous := (14008)
      next := (0)
      square := (325226331536019311607699224280000000000000)
      linear := (-2075946901479912290566787245932000000000000)
      constant := (3432679878160743694079197864110999827214633) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree012.table
  base := (962463709558231767387636965639021104071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (6800)
      previous := (4760)
      next := (0)
      square := (108408777178673103869233074760000000000000)
      linear := (-712388658550466092878039621540000000000000)
      constant := (1151365412191561367378944052109677099076519) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (162740845680329874321/100000000000000000000)
  centralHi := (81370422840164937161/50000000000000000000)
  directionLo := (21247158708209833911/12500000000000000000)
  directionHi := (169977269665678671289/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree013.table
  base := (20844799938194764615139789956304407177/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3251250000000000000000000000000000000000000
      center := (7752)
      previous := (5253)
      next := (0)
      square := (121959874326007241852887209105000000000000)
      linear := (-877004535549702371008407041050500000000000)
      constant := (1296576322014237216348679159547047763067377) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree013.table
  base := (-13750527172911103772191008892270561553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (6800)
      previous := (4760)
      next := (0)
      square := (108408777178673103869233074760000000000000)
      linear := (-801666475050549825476231565460000000000000)
      constant := (1180956731164705531392574305970133807711183) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21247158708209833911/12500000000000000000)
  centralHi := (169977269665678671289/100000000000000000000)
  directionLo := (88458975736282339231/50000000000000000000)
  directionHi := (176917951472564678463/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree014.table
  base := (-701678491256598812747839587939291836689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (62016)
      previous := (42024)
      next := (0)
      square := (975678994608057934823097672840000000000000)
      linear := (-7804231864355501064434150919012000000000000)
      constant := (11106919202303432190735463849880301932771911) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree014.table
  base := (-215916158475218734397591229266638122889/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 722500000000000000000000000000000000000000
      center := (1700)
      previous := (1190)
      next := (0)
      square := (27102194294668275967308268690000000000000)
      linear := (-222736072887658389518605877345000000000000)
      constant := (320952560390436022949299522831941582485079) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88458975736282339231/50000000000000000000)
  centralHi := (176917951472564678463/100000000000000000000)
  directionLo := (183596434887768597879/100000000000000000000)
  directionHi := (4589910872194214947/2500000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree015.table
  base := (-366828608340337366807731801668548581763/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2167500000000000000000000000000000000000000
      center := (5168)
      previous := (3502)
      next := (0)
      square := (81306582884004827901924806070000000000000)
      linear := (-716035620359448596733420459135000000000000)
      constant := (1035581857582724297679076999748368379611479) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree015.table
  base := (-100882916341640170517165030770599558931/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 361250000000000000000000000000000000000000
      center := (850)
      previous := (595)
      next := (0)
      square := (13551097147334137983654134345000000000000)
      linear := (-122527763506339661334076931662500000000000)
      constant := (181520857086218570408346750152093454937882) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (183596434887768597879/100000000000000000000)
  centralHi := (4589910872194214947/2500000000000000000)
  directionLo := (190040364801135230421/100000000000000000000)
  directionHi := (95020182400567615211/50000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree016.table
  base := (-537430136555212311273474826021673980097/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6502500000000000000000000000000000000000000
      center := (15504)
      previous := (10506)
      next := (0)
      square := (243919748652014483705774418210000000000000)
      linear := (-2345155756067816314291985025057000000000000)
      constant := (3570473840147664920840071391831225977767703) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree016.table
  base := (-2283655912338542168771946164881327756349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (6800)
      previous := (4760)
      next := (0)
      square := (108408777178673103869233074760000000000000)
      linear := (-1069499924550801023270807397220000000000000)
      constant := (1680674498135025442539639719309296278415139) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (190040364801135230421/100000000000000000000)
  centralHi := (95020182400567615211/50000000000000000000)
  directionLo := (196272844795194381291/100000000000000000000)
  directionHi := (49068211198798595323/25000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree017.table
  base := (-1381420404651479386904278435710655908041/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 765000000000000000000000000000000000000000
      center := (1824)
      previous := (1236)
      next := (0)
      square := (28696441017884056906561696260000000000000)
      linear := (-299082900124386686868671608554000000000000)
      constant := (489276180014747971538688064196669646069727) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree017.table
  base := (-2885515827181702596176031707207654660903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (400)
      previous := (280)
      next := (0)
      square := (6376986892863123757013710280000000000000)
      linear := (-68163396532404985639352902420000000000000)
      constant := (115617648914452891246805974197469870764649) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (196272844795194381291/100000000000000000000)
  centralHi := (49068211198798595323/25000000000000000000)
  directionLo := (8092536705310479197/4000000000000000000)
  directionHi := (101156708816380989963/50000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree018.table
  base := (-3316976384314598621807829842377022159933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (20672)
      previous := (14008)
      next := (0)
      square := (325226331536019311607699224280000000000000)
      linear := (-3652338061395676483300576427148000000000000)
      constant := (6486891083041768406840066361838321787338089) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree018.table
  base := (-214348363441096155952008625014885753991/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 361250000000000000000000000000000000000000
      center := (850)
      previous := (595)
      next := (0)
      square := (13551097147334137983654134345000000000000)
      linear := (-156006944693871061058398910632500000000000)
      constant := (287973971962863162892948114096396034193202) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8092536705310479197/4000000000000000000)
  centralHi := (101156708816380989963/50000000000000000000)
  directionLo := (208178789276185074791/100000000000000000000)
  directionHi := (26022348659523134349/12500000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree019.table
  base := (-3820008488116748055804176898384212962023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (62016)
      previous := (42024)
      next := (0)
      square := (975678994608057934823097672840000000000000)
      linear := (-11745209764144911546268623872052000000000000)
      constant := (22737245701406875175255595245409062085778177) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree019.table
  base := (-1961718840649187378180703664293001991411/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (3400)
      previous := (2380)
      next := (0)
      square := (54204388589336551934616537380000000000000)
      linear := (-668666687025526110532691614490000000000000)
      constant := (1346675537432801002525789826649322424482221) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (208178789276185074791/100000000000000000000)
  centralHi := (26022348659523134349/12500000000000000000)
  directionLo := (213883373955873844073/100000000000000000000)
  directionHi := (106941686977936922037/50000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree020.table
  base := (-4278160468046748792768590934996674356659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (62016)
      previous := (42024)
      next := (0)
      square := (975678994608057934823097672840000000000000)
      linear := (-12533405344102793642635518462660000000000000)
      constant := (26448920550921715090680030141033649998329941) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree020.table
  base := (-2186579648182113301025946989669025511973/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (3400)
      previous := (2380)
      next := (0)
      square := (54204388589336551934616537380000000000000)
      linear := (-713305595275567976831787586450000000000000)
      constant := (1566214469235422428810319046985651627039803) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213883373955873844073/100000000000000000000)
  centralHi := (106941686977936922037/50000000000000000000)
  directionLo := (27429963943707526563/12500000000000000000)
  directionHi := (43887942309932042501/20000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree021.table
  base := (-587059995285844820073739391422382200173/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1083750000000000000000000000000000000000000
      center := (2584)
      previous := (1751)
      next := (0)
      square := (40653291442002413950962403035000000000000)
      linear := (-555066705169194822458433877219500000000000)
      constant := (1274273703781584696523109277640894632450009) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree021.table
  base := (-597959773251672455796192019444752856881/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 361250000000000000000000000000000000000000
      center := (850)
      previous := (595)
      next := (0)
      square := (13551097147334137983654134345000000000000)
      linear := (-189486125881402460782720889602500000000000)
      constant := (452449730446811164798213011762966424361391) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27429963943707526563/12500000000000000000)
  centralHi := (43887942309932042501/20000000000000000000)
  directionLo := (112429396017287202121/50000000000000000000)
  directionHi := (224858792034574404243/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree022.table
  base := (-39680860133424714644473475818876486869/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 3251250000000000000000000000000000000000000
      center := (7752)
      previous := (5253)
      next := (0)
      square := (121959874326007241852887209105000000000000)
      linear := (-1763724563002319729421163455484500000000000)
      constant := (4390913801195182820897570534011836122459696) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree022.table
  base := (-5159107783132115370013625224513675948661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (6800)
      previous := (4760)
      next := (0)
      square := (108408777178673103869233074760000000000000)
      linear := (-1605166823551303418859959060740000000000000)
      constant := (4153669008072400039424682448555547650836971) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112429396017287202121/50000000000000000000)
  centralHi := (224858792034574404243/100000000000000000000)
  directionLo := (230150311113189428659/100000000000000000000)
  directionHi := (11507515555659471433/5000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree023.table
  base := (-5429695458471261382398953295677345639227/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (62016)
      previous := (42024)
      next := (0)
      square := (975678994608057934823097672840000000000000)
      linear := (-14897992083976439931736202234484000000000000)
      constant := (40073977659016740540111970769172823992370573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree023.table
  base := (-220117023908103183693283480749444279919/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (1360)
      previous := (952)
      next := (0)
      square := (21681755435734620773846614952000000000000)
      linear := (-338888928010277430291630200932000000000000)
      constant := (946727486315947375789204518345053015517045) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (230150311113189428659/100000000000000000000)
  centralHi := (11507515555659471433/5000000000000000000)
  directionLo := (23532287405976451169/10000000000000000000)
  directionHi := (235322874059764511691/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree024.table
  base := (-2875561300792170864123781334633249510799/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (10336)
      previous := (7004)
      next := (0)
      square := (162613165768009655803849612140000000000000)
      linear := (-2614364610655720338017182804182000000000000)
      constant := (7569125098209939198610756233743372674137267) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree024.table
  base := (-727262992589542705683384747767346879469/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 361250000000000000000000000000000000000000
      center := (850)
      previous := (595)
      next := (0)
      square := (13551097147334137983654134345000000000000)
      linear := (-222965307068933860507042868572500000000000)
      constant := (669830514527492037495080163915236751833459) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23532287405976451169/10000000000000000000)
  centralHi := (235322874059764511691/100000000000000000000)
  directionLo := (240384160056351660591/100000000000000000000)
  directionHi := (15024010003521978787/6250000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree025.table
  base := (-6046019236122080026552531175229223253911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (62016)
      previous := (42024)
      next := (0)
      square := (975678994608057934823097672840000000000000)
      linear := (-16474383243892204124469991415700000000000000)
      constant := (51142898567348805708587094884728790316577489) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree025.table
  base := (-6107203211891416057900983619192592263029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (6800)
      previous := (4760)
      next := (0)
      square := (108408777178673103869233074760000000000000)
      linear := (-1873000273051554616654534892500000000000000)
      constant := (6027949106474492103737129196553340835984619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (240384160056351660591/100000000000000000000)
  centralHi := (15024010003521978787/6250000000000000000)
  directionLo := (245341055993992976613/100000000000000000000)
  directionHi := (122670527996996488307/50000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree026.table
  base := (-3158313409124536194047423346232509692167/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (31008)
      previous := (21012)
      next := (0)
      square := (487839497304028967411548836420000000000000)
      linear := (-8631289411925043110418443003154000000000000)
      constant := (28626295782900068803369146871480442290673633) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree026.table
  base := (-3186220530198121250252491162899694237199/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (3400)
      previous := (2380)
      next := (0)
      square := (54204388589336551934616537380000000000000)
      linear := (-981139044775819174626363418210000000000000)
      constant := (3370455750866862612696857845501988365449489) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (245341055993992976613/100000000000000000000)
  centralHi := (122670527996996488307/50000000000000000000)
  directionLo := (125099883199883025471/50000000000000000000)
  directionHi := (250199766399766050943/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree027.table
  base := (-328244780198826659780525565693242153371/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2167500000000000000000000000000000000000000
      center := (5168)
      previous := (3502)
      next := (0)
      square := (81306582884004827901924806070000000000000)
      linear := (-1504231200317330693100315049743000000000000)
      constant := (5311563080727371856385149377795595265136715) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree027.table
  base := (-3307872770636585986591074471605311105749/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (3400)
      previous := (2380)
      next := (0)
      square := (54204388589336551934616537380000000000000)
      linear := (-1025777953025861040925459390170000000000000)
      constant := (3748487047045198112979206082776065090438539) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (125099883199883025471/50000000000000000000)
  centralHi := (250199766399766050943/100000000000000000000)
  directionLo := (63741476124629501733/25000000000000000000)
  directionHi := (254965904498518006933/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree028.table
  base := (-849065973517151987454513134017204004757/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3251250000000000000000000000000000000000000
      center := (7752)
      previous := (5253)
      next := (0)
      square := (121959874326007241852887209105000000000000)
      linear := (-2354871247970731301696334398440500000000000)
      constant := (8824620920921723499173993323926452383627043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree028.table
  base := (-6838797289146160892942706312013359200371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (6800)
      previous := (4760)
      next := (0)
      square := (108408777178673103869233074760000000000000)
      linear := (-2140833722551805814449110724260000000000000)
      constant := (8295651180138181700915264219268139191092781) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63741476124629501733/25000000000000000000)
  centralHi := (254965904498518006933/100000000000000000000)
  directionLo := (8113892756925975621/3125000000000000000)
  directionHi := (259644568221631219873/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree029.table
  base := (-1750253067855514412243296913688780954829/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6502500000000000000000000000000000000000000
      center := (15504)
      previous := (10506)
      next := (0)
      square := (243919748652014483705774418210000000000000)
      linear := (-4906791390930933127484392444533000000000000)
      constant := (19455837532759746808253974792360080736489771) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree029.table
  base := (-1760765967089823663578418792834230749529/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 722500000000000000000000000000000000000000
      center := (1700)
      previous := (1190)
      next := (0)
      square := (27102194294668275967308268690000000000000)
      linear := (-557527884762972386761825667045000000000000)
      constant := (2284129658445410242811490714635907313386119) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8113892756925975621/3125000000000000000)
  centralHi := (259644568221631219873/100000000000000000000)
  directionLo := (10569616163872533937/4000000000000000000)
  directionHi := (132120202048406674213/50000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree030.table
  base := (-719165332878188857097826412139344446811/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (10336)
      previous := (7004)
      next := (0)
      square := (162613165768009655803849612140000000000000)
      linear := (-3402560190613602434384077394790000000000000)
      constant := (14235752140096158472373230101235941823074315) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree030.table
  base := (-1807457083247932173452850640278120129031/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 722500000000000000000000000000000000000000
      center := (1700)
      previous := (1190)
      next := (0)
      square := (27102194294668275967308268690000000000000)
      linear := (-579847338887993319911373653025000000000000)
      constant := (2504801413097974528949320947209623282710041) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10569616163872533937/4000000000000000000)
  centralHi := (132120202048406674213/50000000000000000000)
  directionLo := (268757661300095995037/100000000000000000000)
  directionHi := (134378830650047997519/50000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree031.table
  base := (-7365594673200788308089117822939758836459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (62016)
      previous := (42024)
      next := (0)
      square := (975678994608057934823097672840000000000000)
      linear := (-21203556723639496702671358959348000000000000)
      constant := (93367480698516087647081716409680087266370141) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree031.table
  base := (-59201706748621987384979884105944915503/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (1360)
      previous := (952)
      next := (0)
      square := (21681755435734620773846614952000000000000)
      linear := (-481733434410411402448737311204000000000000)
      constant := (2188677557414908930118360093586547985490825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268757661300095995037/100000000000000000000)
  centralHi := (134378830650047997519/50000000000000000000)
  directionLo := (273200237660487807227/100000000000000000000)
  directionHi := (68300059415121951807/25000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree032.table
  base := (-3761919962800178802169467275322212644003/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (31008)
      previous := (21012)
      next := (0)
      square := (487839497304028967411548836420000000000000)
      linear := (-10995876151798689399519126774978000000000000)
      constant := (50839821643419657068156295166595724912948197) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree032.table
  base := (-1511040352642416677659247422124294090643/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (1360)
      previous := (952)
      next := (0)
      square := (21681755435734620773846614952000000000000)
      linear := (-499588997710428148968375699988000000000000)
      constant := (2381756198079040747364252282974079007804173) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273200237660487807227/100000000000000000000)
  centralHi := (68300059415121951807/25000000000000000000)
  directionLo := (55514343806982686611/20000000000000000000)
  directionHi := (8674116219841044783/3125000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree033.table
  base := (-1916817549472737186718118795458050467299/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2167500000000000000000000000000000000000000
      center := (5168)
      previous := (3502)
      next := (0)
      square := (81306582884004827901924806070000000000000)
      linear := (-1898328990296271741283762345047000000000000)
      constant := (9195725736122317000255706611335670244851767) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree033.table
  base := (-7695654389150048984141712814066277233613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (6800)
      previous := (4760)
      next := (0)
      square := (108408777178673103869233074760000000000000)
      linear := (-2587222805052224477440070443860000000000000)
      constant := (12915136491947089225385849601474845879485843) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55514343806982686611/20000000000000000000)
  centralHi := (8674116219841044783/3125000000000000000)
  directionLo := (7046885329626434867/2500000000000000000)
  directionHi := (281875413185057394681/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree034.table
  base := (-389832965089925915233188872725112009943/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 382500000000000000000000000000000000000000
      center := (912)
      previous := (618)
      next := (0)
      square := (14348220508942028453280848130000000000000)
      linear := (-346590345051663867526059451929000000000000)
      constant := (1755480362560328591344822224436089312393605) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree034.table
  base := (-7822325304643114697632284041273237868911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (400)
      previous := (280)
      next := (0)
      square := (6376986892863123757013710280000000000000)
      linear := (-157441213032488718237544846340000000000000)
      constant := (821308021274736849091191805178354956228513) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7046885329626434867/2500000000000000000)
  centralHi := (281875413185057394681/100000000000000000000)
  directionLo := (286114379066304061953/100000000000000000000)
  directionHi := (143057189533152030977/50000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree035.table
  base := (-3956343484389971642188602391141639504187/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (31008)
      previous := (21012)
      next := (0)
      square := (487839497304028967411548836420000000000000)
      linear := (-12178169521735512544069468660890000000000000)
      constant := (64374871383611798833558438435610595649609613) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree035.table
  base := (-1587175044483066811806574806194664471631/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (1360)
      previous := (952)
      next := (0)
      square := (21681755435734620773846614952000000000000)
      linear := (-553155687610478388527290866340000000000000)
      constant := (3009977930717652778813586371709741967698641) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286114379066304061953/100000000000000000000)
  centralHi := (143057189533152030977/50000000000000000000)
  directionLo := (290291452266074544693/100000000000000000000)
  directionHi := (145145726133037272347/50000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree036.table
  base := (-8015950380551964137305499540127740407017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (20672)
      previous := (14008)
      next := (0)
      square := (325226331536019311607699224280000000000000)
      linear := (-8381511541142969061501943970796000000000000)
      constant := (46159463301062107485420984415826049067116261) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree036.table
  base := (-8036883113672974185476272011786895898853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (6800)
      previous := (4760)
      next := (0)
      square := (108408777178673103869233074760000000000000)
      linear := (-2855056254552475675234646275620000000000000)
      constant := (16177929045021690407087487025953587085231483) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (290291452266074544693/100000000000000000000)
  centralHi := (145145726133037272347/50000000000000000000)
  directionLo := (9200289599774736623/3125000000000000000)
  directionHi := (294409267192791571937/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree037.table
  base := (-2026743562505104215887319097270490722147/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6502500000000000000000000000000000000000000
      center := (15504)
      previous := (10506)
      next := (0)
      square := (243919748652014483705774418210000000000000)
      linear := (-6483182550846697320218181625749000000000000)
      constant := (37139310320930609785656110414260853631695653) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree037.table
  base := (-8125856361517889632196786300254328620221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (6800)
      previous := (4760)
      next := (0)
      square := (108408777178673103869233074760000000000000)
      linear := (-2944334071052559407832838219540000000000000)
      constant := (17346207902254370007146211086766499028756131) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9200289599774736623/3125000000000000000)
  centralHi := (294409267192791571937/100000000000000000000)
  directionLo := (298470276508811583329/100000000000000000000)
  directionHi := (29847027650881158333/10000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree038.table
  base := (-8186219649284514381586985340563501208117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (62016)
      previous := (42024)
      next := (0)
      square := (975678994608057934823097672840000000000000)
      linear := (-26720925783344671377239621093604000000000000)
      constant := (158985097660301894925238893620219933357687683) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree038.table
  base := (-2050809909263601112150946874597955213877/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 722500000000000000000000000000000000000000
      center := (1700)
      previous := (1190)
      next := (0)
      square := (27102194294668275967308268690000000000000)
      linear := (-758402971888160785107757540865000000000000)
      constant := (4638649428834288260991198984251190943189547) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (298470276508811583329/100000000000000000000)
  centralHi := (29847027650881158333/10000000000000000000)
  directionLo := (302476768214513207693/100000000000000000000)
  directionHi := (151238384107256603847/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree039.table
  base := (-1650818349826534345610187447458109669723/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (20672)
      previous := (14008)
      next := (0)
      square := (325226331536019311607699224280000000000000)
      linear := (-9169707121100851157868838561404000000000000)
      constant := (56586968394568007431275222878365894581750795) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree039.table
  base := (-4134711332717593501185841554976737341347/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (3400)
      previous := (2380)
      next := (0)
      square := (54204388589336551934616537380000000000000)
      linear := (-1561444852026363436514611053690000000000000)
      constant := (9901492926850459179642668904041722908350717) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (302476768214513207693/100000000000000000000)
  centralHi := (151238384107256603847/50000000000000000000)
  directionLo := (306430880721487095101/100000000000000000000)
  directionHi := (153215440360743547551/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree040.table
  base := (-8310946609472582914220055328981303136183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (62016)
      previous := (42024)
      next := (0)
      square := (975678994608057934823097672840000000000000)
      linear := (-28297316943260435569973410274820000000000000)
      constant := (180883737742108909125048287329159630542788017) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree040.table
  base := (-1040593378069845310157252707785286374407/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 361250000000000000000000000000000000000000
      center := (850)
      previous := (595)
      next := (0)
      square := (13551097147334137983654134345000000000000)
      linear := (-401520940069101325703426756412500000000000)
      constant := (2636409200166624021730738146950052237796377) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (306430880721487095101/100000000000000000000)
  centralHi := (153215440360743547551/50000000000000000000)
  directionLo := (62066923239353875781/20000000000000000000)
  directionHi := (155167308098384689453/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree041.table
  base := (-2089274285053634648458881339203746975767/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6502500000000000000000000000000000000000000
      center := (15504)
      previous := (10506)
      next := (0)
      square := (243919748652014483705774418210000000000000)
      linear := (-7271378130804579416585076216357000000000000)
      constant := (48088195364209972357131481397399654116030033) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree041.table
  base := (-8369512099212448904746816193700822065037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (6800)
      previous := (4760)
      next := (0)
      square := (108408777178673103869233074760000000000000)
      linear := (-3301445337052894338225605995220000000000000)
      constant := (22419374436029839580015618271480462423204307) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62066923239353875781/20000000000000000000)
  centralHi := (155167308098384689453/50000000000000000000)
  directionLo := (157094926207250610879/50000000000000000000)
  directionHi := (314189852414501221759/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree042.table
  base := (-8392818335830807825076187635916711110547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (20672)
      previous := (14008)
      next := (0)
      square := (325226331536019311607699224280000000000000)
      linear := (-9957902701058733254235733152012000000000000)
      constant := (68055773689091530461311806585591411467155751) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree042.table
  base := (-4201990148466405306103687079950349227633/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (3400)
      previous := (2380)
      next := (0)
      square := (54204388589336551934616537380000000000000)
      linear := (-1695361576776489035411898969570000000000000)
      constant := (11893606261006696741858373620514349073214063) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157094926207250610879/50000000000000000000)
  centralHi := (314189852414501221759/100000000000000000000)
  directionLo := (158999176657063198683/50000000000000000000)
  directionHi := (317998353314126397367/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree043.table
  base := (-4209175936609845848713649818535363971389/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (31008)
      previous := (21012)
      next := (0)
      square := (487839497304028967411548836420000000000000)
      linear := (-15330951841567040929537047023322000000000000)
      constant := (108163363985900266928762807574588318310417211) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree043.table
  base := (-8428381617928817646624060480478223215137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (6800)
      previous := (4760)
      next := (0)
      square := (108408777178673103869233074760000000000000)
      linear := (-3480000970053061803421989883060000000000000)
      constant := (25194721389223261542526810622481793490825407) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158999176657063198683/50000000000000000000)
  centralHi := (317998353314126397367/100000000000000000000)
  directionLo := (321761778433588763277/100000000000000000000)
  directionHi := (160880889216794381639/50000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree044.table
  base := (-8433910150991774105149315950075102490473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (62016)
      previous := (42024)
      next := (0)
      square := (975678994608057934823097672840000000000000)
      linear := (-31450099263091963955440988637252000000000000)
      constant := (228830449721631588140325069378741058422279727) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree044.table
  base := (-8442917659533824667289510138171090985583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (6800)
      previous := (4760)
      next := (0)
      square := (108408777178673103869233074760000000000000)
      linear := (-3569278786553145536020181826980000000000000)
      constant := (26641842776030104259910236905828554705166513) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (321761778433588763277/100000000000000000000)
  centralHi := (160880889216794381639/50000000000000000000)
  directionLo := (162740845680329874321/50000000000000000000)
  directionHi := (325481691360659748643/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree045.table
  base := (-1687935967688164368566382987580582723499/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (20672)
      previous := (14008)
      next := (0)
      square := (325226331536019311607699224280000000000000)
      linear := (-10746098281016615350602627742620000000000000)
      constant := (80559333596644888933202009674458173893631835) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree045.table
  base := (-4223882562717171272334303706078224825773/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (3400)
      previous := (2380)
      next := (0)
      square := (54204388589336551934616537380000000000000)
      linear := (-1829278301526614634309186885450000000000000)
      constant := (14064262807534259997151337267193393025351603) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (162740845680329874321/50000000000000000000)
  centralHi := (325481691360659748643/100000000000000000000)
  directionLo := (82289891831122579689/25000000000000000000)
  directionHi := (329159567324490318757/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree046.table
  base := (-8435824993957335647629271976090410057149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (62016)
      previous := (42024)
      next := (0)
      square := (975678994608057934823097672840000000000000)
      linear := (-33026490423007728148174777818468000000000000)
      constant := (254868954460836077418030483931307243441355451) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree046.table
  base := (-2110769725270498123212444464958868536061/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 722500000000000000000000000000000000000000
      center := (1700)
      previous := (1190)
      next := (0)
      square := (27102194294668275967308268690000000000000)
      linear := (-936958604888328250304141428705000000000000)
      constant := (7413681286110747553708142130516886993078371) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82289891831122579689/25000000000000000000)
  centralHi := (329159567324490318757/100000000000000000000)
  directionLo := (332796800031934770139/100000000000000000000)
  directionHi := (16639840001596738507/5000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree047.table
  base := (-8422489805262501887741078726418474407399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (62016)
      previous := (42024)
      next := (0)
      square := (975678994608057934823097672840000000000000)
      linear := (-33814686002965610244541672409076000000000000)
      constant := (268402935702073014251911036090247148066355201) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree047.table
  base := (-421449737450656699863056507958451415937/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 144500000000000000000000000000000000000000
      center := (340)
      previous := (238)
      next := (0)
      square := (5420438858933655193461653738000000000000)
      linear := (-191855611802669836690737882937000000000000)
      constant := (1561020106439025351510559773047007540794207) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (332796800031934770139/100000000000000000000)
  centralHi := (16639840001596738507/5000000000000000000)
  directionLo := (4204933847981170279/1250000000000000000)
  directionHi := (336394707838493622321/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree048.table
  base := (-8399800997410408251167409666109560560283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (20672)
      previous := (14008)
      next := (0)
      square := (325226331536019311607699224280000000000000)
      linear := (-11534293860974497446969522333228000000000000)
      constant := (94093204967259931741586497261646210994234639) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree048.table
  base := (-2101407917776877950374198201727101668937/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 722500000000000000000000000000000000000000
      center := (1700)
      previous := (1190)
      next := (0)
      square := (27102194294668275967308268690000000000000)
      linear := (-981597513138370116603237400665000000000000)
      constant := (8206380544134456052384963053860867617677207) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4204933847981170279/1250000000000000000)
  centralHi := (336394707838493622321/100000000000000000000)
  directionLo := (21247158708209833911/6250000000000000000)
  directionHi := (339954539331357342577/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree049.table
  base := (-4183934974444587751664060855992983553033/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (31008)
      previous := (21012)
      next := (0)
      square := (487839497304028967411548836420000000000000)
      linear := (-17695538581440687218637730795146000000000000)
      constant := (148249351182254409112859401587363449778561167) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree049.table
  base := (-8373093978974382148488667103516609443607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (6800)
      previous := (4760)
      next := (0)
      square := (108408777178673103869233074760000000000000)
      linear := (-4015667869053564199011141546580000000000000)
      constant := (34470055141659866698611219309743699870797577) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21247158708209833911/6250000000000000000)
  centralHi := (339954539331357342577/100000000000000000000)
  directionLo := (343477478391590167259/100000000000000000000)
  directionHi := (17173873919579508363/5000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree050.table
  base := (-4163397275617576296423479756652382222693/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (31008)
      previous := (21012)
      next := (0)
      square := (487839497304028967411548836420000000000000)
      linear := (-18089636371419628266821178090450000000000000)
      constant := (155529971737187019819709305213447153838775507) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree050.table
  base := (-1041434138568408322714459780409849170129/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 361250000000000000000000000000000000000000
      center := (850)
      previous := (595)
      next := (0)
      square := (13551097147334137983654134345000000000000)
      linear := (-513118210694205991451166686312500000000000)
      constant := (4519246824895230846419985920336553589832719) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (343477478391590167259/100000000000000000000)
  centralHi := (17173873919579508363/5000000000000000000)
  directionLo := (346964648793641791319/100000000000000000000)
  directionHi := (8674116219841044783/2500000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree051.table
  base := (-258645651352048092957973383694653870723/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 63750000000000000000000000000000000000000
      center := (152)
      previous := (103)
      next := (0)
      square := (2391370084823671408880141355000000000000)
      linear := (-90606540006855731936297183263500000000000)
      constant := (798929202069637067851918619546590610372508) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree051.table
  base := (-8280849210500180477905736294177300817277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (400)
      previous := (280)
      next := (0)
      square := (6376986892863123757013710280000000000000)
      linear := (-246719029532572450835736790260000000000000)
      constant := (2228073963852880822583028844978985886106291) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (346964648793641791319/100000000000000000000)
  centralHi := (8674116219841044783/2500000000000000000)
  directionLo := (70083423678568985287/20000000000000000000)
  directionHi := (87604279598211231609/25000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree052.table
  base := (-4108772223627631500178249372647365021689/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (31008)
      previous := (21012)
      next := (0)
      square := (487839497304028967411548836420000000000000)
      linear := (-18877831951377510363188072681058000000000000)
      constant := (170604009290542690857844925244069003578586911) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree052.table
  base := (-1027661568023324709881235849940776778583/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 361250000000000000000000000000000000000000
      center := (850)
      previous := (595)
      next := (0)
      square := (13551097147334137983654134345000000000000)
      linear := (-535437664819226924600714672292500000000000)
      constant := (4954985399464761799491327019197115510989513) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70083423678568985287/20000000000000000000)
  centralHi := (87604279598211231609/25000000000000000000)
  directionLo := (14153436117805174277/4000000000000000000)
  directionHi := (176917951472564678463/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree053.table
  base := (-4074755915533318992572837228249222131799/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (31008)
      previous := (21012)
      next := (0)
      square := (487839497304028967411548836420000000000000)
      linear := (-19271929741356451411371519976362000000000000)
      constant := (178397241500742268401459225846774573235190801) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree053.table
  base := (-815286469937679384387107345915690404617/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 289000000000000000000000000000000000000000
      center := (680)
      previous := (476)
      next := (0)
      square := (10840877717867310386923307476000000000000)
      linear := (-437277913505389912940390932226000000000000)
      constant := (4144183423037559834204633400024365473065687) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14153436117805174277/4000000000000000000)
  centralHi := (176917951472564678463/50000000000000000000)
  directionLo := (357221969597678728499/100000000000000000000)
  directionHi := (714443939195357457/200000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree054.table
  base := (-4036310708663751150802312845440115290119/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (10336)
      previous := (7004)
      next := (0)
      square := (162613165768009655803849612140000000000000)
      linear := (-6555342510445130819851655757222000000000000)
      constant := (62120392624725730223030491285909820043466827) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree054.table
  base := (-504726229191772871034857805823726180951/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 361250000000000000000000000000000000000000
      center := (850)
      previous := (595)
      next := (0)
      square := (13551097147334137983654134345000000000000)
      linear := (-557757118944247857750262658272500000000000)
      constant := (5410386860759147537451023504178886267410322) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (357221969597678728499/100000000000000000000)
  centralHi := (714443939195357457/200000000000000000)
  directionLo := (360576240084527490887/100000000000000000000)
  directionHi := (45072030010565936361/12500000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree055.table
  base := (-7986924558195183258554294900621610499159/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (62016)
      previous := (42024)
      next := (0)
      square := (975678994608057934823097672840000000000000)
      linear := (-40120250642628667015476829133940000000000000)
      constant := (388991503254733706991240067235743191091687441) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree055.table
  base := (-9987005972519375149039434850430597017/12500000000000000000000000000000000000)
  polynomial :=
    { denominator := 72250000000000000000000000000000000000000
      center := (170)
      previous := (119)
      next := (0)
      square := (2710219429466827596730826869000000000000)
      linear := (-113783369201351664865007330252500000000000)
      constant := (1129091287105572011694075124852011149241740) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360576240084527490887/100000000000000000000)
  centralHi := (45072030010565936361/12500000000000000000)
  directionLo := (363899593657020608621/100000000000000000000)
  directionHi := (181949796828510304311/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree056.table
  base := (-3946233195998071867390786628639165269343/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (31008)
      previous := (21012)
      next := (0)
      square := (487839497304028967411548836420000000000000)
      linear := (-20454223111293274555921861862274000000000000)
      constant := (202800904057917691907182553158592731134438857) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree056.table
  base := (-986857690664831374630561485559314128193/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 361250000000000000000000000000000000000000
      center := (850)
      previous := (595)
      next := (0)
      square := (13551097147334137983654134345000000000000)
      linear := (-580076573069268790899810644252500000000000)
      constant := (5885436504164833433202733935893358216952223) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363899593657020608621/100000000000000000000)
  centralHi := (181949796828510304311/50000000000000000000)
  directionLo := (183596434887768597879/50000000000000000000)
  directionHi := (367192869775537195759/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree057.table
  base := (-778928659605654026147144332439079304841/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (10336)
      previous := (7004)
      next := (0)
      square := (162613165768009655803849612140000000000000)
      linear := (-6949440300424071868035103052526000000000000)
      constant := (70425527855155679778324320885336191213514265) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree057.table
  base := (-311657051415891360666540043770928054199/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (1360)
      previous := (952)
      next := (0)
      square := (21681755435734620773846614952000000000000)
      linear := (-945978080210846811959335419588000000000000)
      constant := (9808521204115063155819608128419008961682445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (183596434887768597879/50000000000000000000)
  centralHi := (367192869775537195759/100000000000000000000)
  directionLo := (370456870585827468923/100000000000000000000)
  directionHi := (92614217646456867231/25000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree058.table
  base := (-3838710024151931814635646420888773193773/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (31008)
      previous := (21012)
      next := (0)
      square := (487839497304028967411548836420000000000000)
      linear := (-21242418691251156652288756452882000000000000)
      constant := (219922744791270194005754334354485100922996427) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree058.table
  base := (-7679330949898892753177794086765145823401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (6800)
      previous := (4760)
      next := (0)
      square := (108408777178673103869233074760000000000000)
      linear := (-4819168217554317792394869041860000000000000)
      constant := (51040984229306699764990728290164872857037111) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370456870585827468923/100000000000000000000)
  centralHi := (92614217646456867231/25000000000000000000)
  directionLo := (93423090800165146197/25000000000000000000)
  directionHi := (373692363200660584789/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree059.table
  base := (-1511379481739038242448755945636629505817/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (62016)
      previous := (42024)
      next := (0)
      square := (975678994608057934823097672840000000000000)
      linear := (-43273032962460195400944407496372000000000000)
      constant := (457478695724105953589116363261390033276849915) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree059.table
  base := (-3779301739773363965478085414740202979543/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (3400)
      previous := (2380)
      next := (0)
      square := (54204388589336551934616537380000000000000)
      linear := (-2454223017027200762496530492890000000000000)
      constant := (26539309289431899981978675620370081338912073) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93423090800165146197/25000000000000000000)
  centralHi := (373692363200660584789/100000000000000000000)
  directionLo := (37690008180517065139/10000000000000000000)
  directionHi := (376900081805170651391/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree060.table
  base := (-7427745630187782820974102744636459373043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (20672)
      previous := (14008)
      next := (0)
      square := (325226331536019311607699224280000000000000)
      linear := (-14687076180806025832437100695660000000000000)
      constant := (158484238483662980878478968997280189723571719) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree060.table
  base := (-7429268389569510562413792020485551417607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (6800)
      previous := (4760)
      next := (0)
      square := (108408777178673103869233074760000000000000)
      linear := (-4997723850554485257591252929700000000000000)
      constant := (55155501984345516003409928052079675640311577) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (37690008180517065139/10000000000000000000)
  centralHi := (376900081805170651391/100000000000000000000)
  directionLo := (190040364801135230421/50000000000000000000)
  directionHi := (380080729602270460843/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree061.table
  base := (-455624275486897347311093674658091918047/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3251250000000000000000000000000000000000000
      center := (7752)
      previous := (5253)
      next := (0)
      square := (121959874326007241852887209105000000000000)
      linear := (-5606178015296994949209774584698500000000000)
      constant := (61720935891558959595928646089324905842319506) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree061.table
  base := (-7291347175165154201712819650088832018557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (6800)
      previous := (4760)
      next := (0)
      square := (108408777178673103869233074760000000000000)
      linear := (-5087001667054568990189444873620000000000000)
      constant := (57271628233639650866195593908984327546637027) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (190040364801135230421/50000000000000000000)
  centralHi := (380080729602270460843/100000000000000000000)
  directionLo := (76646996122547199761/20000000000000000000)
  directionHi := (191617490306367999403/50000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree062.table
  base := (-7143646573198694113377797675868806264613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (62016)
      previous := (42024)
      next := (0)
      square := (975678994608057934823097672840000000000000)
      linear := (-45637619702333841690045091268196000000000000)
      constant := (512422956585313435604278067125050834905741587) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree062.table
  base := (-7144858684406435583069982067075401591933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (6800)
      previous := (4760)
      next := (0)
      square := (108408777178673103869233074760000000000000)
      linear := (-5176279483554652722787636817540000000000000)
      constant := (59426991879653172076125714318655208939931363) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76646996122547199761/20000000000000000000)
  centralHi := (191617490306367999403/50000000000000000000)
  directionLo := (386363481343014664519/100000000000000000000)
  directionHi := (9659087033575366613/2500000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree063.table
  base := (-6988738441609895909627921214241456857459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (20672)
      previous := (14008)
      next := (0)
      square := (325226331536019311607699224280000000000000)
      linear := (-15475271760763907928803995286268000000000000)
      constant := (177139692057228851050662184184947856904583047) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree063.table
  base := (-1747454861270360910279976807015082494571/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 722500000000000000000000000000000000000000
      center := (1700)
      previous := (1190)
      next := (0)
      square := (27102194294668275967308268690000000000000)
      linear := (-1316389325013684113846457190365000000000000)
      constant := (15405397036463830482772720450407641159068981) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386363481343014664519/100000000000000000000)
  centralHi := (9659087033575366613/2500000000000000000)
  directionLo := (24341678270777926863/6250000000000000000)
  directionHi := (389466852332446829809/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree064.table
  base := (-1365056023302110652291858499898425984713/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (62016)
      previous := (42024)
      next := (0)
      square := (975678994608057934823097672840000000000000)
      linear := (-47214010862249605882778880449412000000000000)
      constant := (550755804006422407999337193547291370068807435) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree064.table
  base := (-3413121975579784404641172804581902662769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (3400)
      previous := (2380)
      next := (0)
      square := (54204388589336551934616537380000000000000)
      linear := (-2677417558277410093992010352690000000000000)
      constant := (31927706421744473297916394235155830130459759) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24341678270777926863/6250000000000000000)
  centralHi := (389466852332446829809/100000000000000000000)
  directionLo := (196272844795194381291/50000000000000000000)
  directionHi := (392545689590388762583/100000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree065.table
  base := (-831660719691470135463761357343974506169/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3251250000000000000000000000000000000000000
      center := (7752)
      previous := (5253)
      next := (0)
      square := (121959874326007241852887209105000000000000)
      linear := (-6000275805275935997393221880002500000000000)
      constant := (71304137907540065284104485709065822309454431) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree065.table
  base := (-6654144913870802652431762296283482432591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (6800)
      previous := (4760)
      next := (0)
      square := (108408777178673103869233074760000000000000)
      linear := (-5444112933054903920582212649300000000000000)
      constant := (66128462299008578508102713914874073576981201) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (196272844795194381291/50000000000000000000)
  centralHi := (392545689590388762583/100000000000000000000)
  directionLo := (98900141483165910207/25000000000000000000)
  directionHi := (395600565932663640829/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree066.table
  base := (-1618191953961694125431068734805272528169/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2167500000000000000000000000000000000000000
      center := (5168)
      previous := (3502)
      next := (0)
      square := (81306582884004827901924806070000000000000)
      linear := (-4065866835180447506292722469219000000000000)
      constant := (49204245128989937849121916040765028718077477) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree066.table
  base := (-6473533481769963457924135216782402746567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (6800)
      previous := (4760)
      next := (0)
      square := (108408777178673103869233074760000000000000)
      linear := (-5533390749554987653180404593220000000000000)
      constant := (68440733290481875182854780514309885606242137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98900141483165910207/25000000000000000000)
  centralHi := (395600565932663640829/100000000000000000000)
  directionLo := (49829004028228513043/12500000000000000000)
  directionHi := (79726406445165620869/20000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree067.table
  base := (-1256747448208942702227005711292694541451/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (62016)
      previous := (42024)
      next := (0)
      square := (975678994608057934823097672840000000000000)
      linear := (-49578597602123252171879564221236000000000000)
      constant := (610809290389217318246576602892972107488429745) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree067.table
  base := (-6284419433617419846991550151299036492179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (6800)
      previous := (4760)
      next := (0)
      square := (108408777178673103869233074760000000000000)
      linear := (-5622668566055071385778596537140000000000000)
      constant := (70792222991847090088552915478014578453760269) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49829004028228513043/12500000000000000000)
  centralHi := (79726406445165620869/20000000000000000000)
  directionLo := (200820309273454436741/50000000000000000000)
  directionHi := (401640618546908873483/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree068.table
  base := (-6086203662937008999410570011821968941537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (3648)
      previous := (2472)
      next := (0)
      square := (57392882035768113813123392520000000000000)
      linear := (-2962752540122419662838026988932000000000000)
      constant := (37147536749246774535286581240124038751944839) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree068.table
  base := (-6086811347434550456036200149530197494123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (400)
      previous := (280)
      next := (0)
      square := (6376986892863123757013710280000000000000)
      linear := (-335996846032656183433928734180000000000000)
      constant := (4304878172003296752898640294977986642599909) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (200820309273454436741/50000000000000000000)
  centralHi := (401640618546908873483/100000000000000000000)
  directionLo := (8092536705310479197/2000000000000000000)
  directionHi := (404626835265523959851/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree069.table
  base := (-5880175551334491971203594826199822303033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (20672)
      previous := (14008)
      next := (0)
      square := (325226331536019311607699224280000000000000)
      linear := (-17051662920679672121537784467484000000000000)
      constant := (217515807520611611502749055335573554063270389) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree069.table
  base := (-735089593584664164569971289380590127073/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 361250000000000000000000000000000000000000
      center := (850)
      previous := (595)
      next := (0)
      square := (13551097147334137983654134345000000000000)
      linear := (-725153024881904856371872553122500000000000)
      constant := (9451606114031495930490337766151509453275903) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8092536705310479197/2000000000000000000)
  centralHi := (404626835265523959851/100000000000000000000)
  directionLo := (203795587027322164201/50000000000000000000)
  directionHi := (407591174054644328403/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree070.table
  base := (-226626414258589872117382750610006132879/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (62016)
      previous := (42024)
      next := (0)
      square := (975678994608057934823097672840000000000000)
      linear := (-51943184341996898460980247993060000000000000)
      constant := (673927164485094373508632826210344351209543025) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree070.table
  base := (-1416535560026920400392522693479851586867/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 722500000000000000000000000000000000000000
      center := (1700)
      previous := (1190)
      next := (0)
      square := (27102194294668275967308268690000000000000)
      linear := (-1472625503888830645893293092225000000000000)
      constant := (19520495262059161943872775978834322891395437) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (203795587027322164201/50000000000000000000)
  centralHi := (407591174054644328403/100000000000000000000)
  directionLo := (205267054417832278579/50000000000000000000)
  directionHi := (410534108835664557159/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree071.table
  base := (-5442664632375931002194181128556414086193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (62016)
      previous := (42024)
      next := (0)
      square := (975678994608057934823097672840000000000000)
      linear := (-52731379921954780557347142583668000000000000)
      constant := (695647333459894526423785478824763166961812007) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree071.table
  base := (-5443093615624002836464364661350769809853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (6800)
      previous := (4760)
      next := (0)
      square := (108408777178673103869233074760000000000000)
      linear := (-5979779832055406316171364312820000000000000)
      constant := (80590323657573463359142298666929627524952483) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205267054417832278579/50000000000000000000)
  centralHi := (410534108835664557159/100000000000000000000)
  directionLo := (206728048331463222193/50000000000000000000)
  directionHi := (413456096662926444387/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree072.table
  base := (-20356227130425323338797644537063050629/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 1083750000000000000000000000000000000000000
      center := (2584)
      previous := (1751)
      next := (0)
      square := (40653291442002413950962403035000000000000)
      linear := (-2229982312579694277238084882261500000000000)
      constant := (29904496437001449711689582702622122723349024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree072.table
  base := (-2605787980016004141525067892381412912693/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (3400)
      previous := (2380)
      next := (0)
      square := (54204388589336551934616537380000000000000)
      linear := (-3034528824277745024384778128370000000000000)
      constant := (41568937635376778930106953111821771668231723) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206728048331463222193/50000000000000000000)
  centralHi := (413456096662926444387/100000000000000000000)
  directionLo := (208178789276185074791/50000000000000000000)
  directionHi := (416357578552370149583/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree073.table
  base := (-621406746176185398003693472706276352359/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3251250000000000000000000000000000000000000
      center := (7752)
      previous := (5253)
      next := (0)
      square := (121959874326007241852887209105000000000000)
      linear := (-6788471385233818093760116470610500000000000)
      constant := (92513611796535747104101555219959675207514241) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree073.table
  base := (-1242898434123343766260868217096170712007/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 722500000000000000000000000000000000000000
      center := (1700)
      previous := (1190)
      next := (0)
      square := (27102194294668275967308268690000000000000)
      linear := (-1539583866263893445341937050165000000000000)
      constant := (21431158649480801647487995681044206664229977) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (208178789276185074791/50000000000000000000)
  centralHi := (416357578552370149583/100000000000000000000)
  directionLo := (83847796051713364869/20000000000000000000)
  directionHi := (209619490129283412173/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree074.table
  base := (-1180712142423411725148552496845464840807/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6502500000000000000000000000000000000000000
      center := (15504)
      previous := (10506)
      next := (0)
      square := (243919748652014483705774418210000000000000)
      linear := (-13773991665457106711611956588873000000000000)
      constant := (190712565374629360905645400647700545949060993) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree074.table
  base := (-147598464474192606760409640567743685791/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 361250000000000000000000000000000000000000
      center := (850)
      previous := (595)
      next := (0)
      square := (13551097147334137983654134345000000000000)
      linear := (-780951660194457189245742518072500000000000)
      constant := (11043825063341552267595335556398688299225604) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83847796051713364869/20000000000000000000)
  centralHi := (209619490129283412173/50000000000000000000)
  directionLo := (211050356502004568013/50000000000000000000)
  directionHi := (422100713004009136027/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree075.table
  base := (-139561933639510481430504948658933473603/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1083750000000000000000000000000000000000000
      center := (2584)
      previous := (1751)
      next := (0)
      square := (40653291442002413950962403035000000000000)
      linear := (-2328506760074429539283946706087500000000000)
      constant := (32747166901842469609869424294238318713544796) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree075.table
  base := (-4466250780427379354117898615551223835963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (6800)
      previous := (4760)
      next := (0)
      square := (108408777178673103869233074760000000000000)
      linear := (-6336891098055741246564132088500000000000000)
      constant := (91015772002919173773675542037605696311406693) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211050356502004568013/50000000000000000000)
  centralHi := (422100713004009136027/100000000000000000000)
  directionLo := (424943174164196678221/100000000000000000000)
  directionHi := (212471587082098339111/50000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree076.table
  base := (-4200657349610392523278912872309690503257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (62016)
      previous := (42024)
      next := (0)
      square := (975678994608057934823097672840000000000000)
      linear := (-56672357821744191039181615536708000000000000)
      constant := (809354117810220575090213327700424895001028543) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree076.table
  base := (-4200896509679074691733273023724939049479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (6800)
      previous := (4760)
      next := (0)
      square := (108408777178673103869233074760000000000000)
      linear := (-6426168914555824979162324032420000000000000)
      constant := (93720148213291344514636616270303492614700569) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (424943174164196678221/100000000000000000000)
  centralHi := (212471587082098339111/50000000000000000000)
  directionLo := (213883373955873844073/50000000000000000000)
  directionHi := (427766747911747688147/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree077.table
  base := (-1963439017773980241183339677654405117169/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (31008)
      previous := (21012)
      next := (0)
      square := (487839497304028967411548836420000000000000)
      linear := (-28730276700851036567774255063658000000000000)
      constant := (416558295036396485522153418581615692290243431) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree077.table
  base := (-3927090705042921634193831531870354491711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (6800)
      previous := (4760)
      next := (0)
      square := (108408777178673103869233074760000000000000)
      linear := (-6515446731055908711760515976340000000000000)
      constant := (96463728370810079096396687804429467551895521) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213883373955873844073/50000000000000000000)
  centralHi := (427766747911747688147/100000000000000000000)
  directionLo := (215285902911246489609/50000000000000000000)
  directionHi := (430571805822492979219/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree078.table
  base := (-3644646617194254912149337783662092941107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (20672)
      previous := (14008)
      next := (0)
      square := (325226331536019311607699224280000000000000)
      linear := (-19416249660553318410638468239308000000000000)
      constant := (285739805151222926882610637876152165420060231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree078.table
  base := (-14237639447506143575983271071567593103/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 361250000000000000000000000000000000000000
      center := (850)
      previous := (595)
      next := (0)
      square := (13551097147334137983654134345000000000000)
      linear := (-825590568444499055544838490032500000000000)
      constant := (12405813975189381365635448404935142898983456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (215285902911246489609/50000000000000000000)
  centralHi := (430571805822492979219/100000000000000000000)
  directionLo := (433358707446259239097/100000000000000000000)
  directionHi := (216679353723129619549/50000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree079.table
  base := (-3353965457888370528279850824851890687207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (62016)
      previous := (42024)
      next := (0)
      square := (975678994608057934823097672840000000000000)
      linear := (-59036944561617837328282299308532000000000000)
      constant := (881662587805803018545375201197978632322574593) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree079.table
  base := (-3354133539862134159305440766864018962913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (6800)
      previous := (4760)
      next := (0)
      square := (108408777178673103869233074760000000000000)
      linear := (-6694002364056076176956899864180000000000000)
      constant := (102068497913064026336699545140436298519718143) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (433358707446259239097/100000000000000000000)
  centralHi := (216679353723129619549/50000000000000000000)
  directionLo := (436127800844823932403/100000000000000000000)
  directionHi := (109031950211205983101/25000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree080.table
  base := (-3054836639992632303318331320660756611461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (62016)
      previous := (42024)
      next := (0)
      square := (975678994608057934823097672840000000000000)
      linear := (-59825140141575719424649193899140000000000000)
      constant := (906446101712971277483307846370321372053589939) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree080.table
  base := (-610997206183161525430923584701711159979/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (1360)
      previous := (952)
      next := (0)
      square := (21681755435734620773846614952000000000000)
      linear := (-1356656036111231981911018361620000000000000)
      constant := (20985937236937465603284014480821205474766069) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (436127800844823932403/100000000000000000000)
  centralHi := (109031950211205983101/25000000000000000000)
  directionLo := (27429963943707526563/6250000000000000000)
  directionHi := (438879423099320425009/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree081.table
  base := (-2747261998819109179845911181523477436831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (20672)
      previous := (14008)
      next := (0)
      square := (325226331536019311607699224280000000000000)
      linear := (-20204445240511200507005362829916000000000000)
      constant := (310523317467175622047325441682147945062267523) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree081.table
  base := (-2747394756506502803638907883498496071199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (6800)
      previous := (4760)
      next := (0)
      square := (108408777178673103869233074760000000000000)
      linear := (-6872557997056243642153283752020000000000000)
      constant := (107830076158382406076944307573928934635423489) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27429963943707526563/6250000000000000000)
  centralHi := (438879423099320425009/100000000000000000000)
  directionLo := (27600868799324209869/6250000000000000000)
  directionHi := (88322780157837471581/20000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree082.table
  base := (-607810788111945822829069915906909208749/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6502500000000000000000000000000000000000000
      center := (15504)
      previous := (10506)
      next := (0)
      square := (243919748652014483705774418210000000000000)
      linear := (-15350382825372870904345745770089000000000000)
      constant := (239258533915710937748066897867750529148043851) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree082.table
  base := (-486272222187699685859944485402669262229/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (1360)
      previous := (952)
      next := (0)
      square := (21681755435734620773846614952000000000000)
      linear := (-1392367162711265474950295139188000000000000)
      constant := (22153933486239064792451156529086628583215819) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27600868799324209869/6250000000000000000)
  centralHi := (88322780157837471581/20000000000000000000)
  directionLo := (88866310088917750319/20000000000000000000)
  directionHi := (111082887611147187899/25000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree083.table
  base := (-2106781527934211612837952667109857587831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (62016)
      previous := (42024)
      next := (0)
      square := (975678994608057934823097672840000000000000)
      linear := (-62189726881449365713749877670964000000000000)
      constant := (982838647785150428341924395787740860414051569) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree083.table
  base := (-2106886321447741136427444130478536412271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (6800)
      previous := (4760)
      next := (0)
      square := (108408777178673103869233074760000000000000)
      linear := (-7051113630056411107349667639860000000000000)
      constant := (113748459648454893095622577054031702976853681) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88866310088917750319/20000000000000000000)
  centralHi := (111082887611147187899/25000000000000000000)
  directionLo := (447032678974079055301/100000000000000000000)
  directionHi := (223516339487039527651/50000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree084.table
  base := (-177387838434418158827525456259684339373/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (10336)
      previous := (7004)
      next := (0)
      square := (162613165768009655803849612140000000000000)
      linear := (-10496320410234541301686128710262000000000000)
      constant := (168163914248936130841575938384776668388818045) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree084.table
  base := (-886985734361985472362488620731511081321/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (3400)
      previous := (2380)
      next := (0)
      square := (54204388589336551934616537380000000000000)
      linear := (-3570195723278247419973929791890000000000000)
      constant := (58383226248920889305675275736088593297498231) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (447032678974079055301/100000000000000000000)
  centralHi := (223516339487039527651/50000000000000000000)
  directionLo := (89943516813829761697/20000000000000000000)
  directionHi := (224858792034574404243/50000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree085.table
  base := (-1432534832999839221211482958736892855313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1530000000000000000000000000000000000000000
      center := (3648)
      previous := (2472)
      next := (0)
      square := (57392882035768113813123392520000000000000)
      linear := (-3750948120080301759204921579540000000000000)
      constant := (60909920346923171727031831644333255393137111) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree085.table
  base := (-1432617504900554765825998837725817589097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (400)
      previous := (280)
      next := (0)
      square := (6376986892863123757013710280000000000000)
      linear := (-425274662532739916032120678100000000000000)
      constant := (7048449747305261027763386660258661100985351) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89943516813829761697/20000000000000000000)
  centralHi := (224858792034574404243/50000000000000000000)
  directionLo := (452386554587160370951/100000000000000000000)
  directionHi := (56548319323395046369/12500000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree086.table
  base := (-1082751855275171213673776951269847587147/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (62016)
      previous := (42024)
      next := (0)
      square := (975678994608057934823097672840000000000000)
      linear := (-64554313621323012002850561442788000000000000)
      constant := (1062294126444828091860208329934737526425830653) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree086.table
  base := (-541412634662408431167088299383966401487/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (3400)
      previous := (2380)
      next := (0)
      square := (54204388589336551934616537380000000000000)
      linear := (-3659473539778331152572121735810000000000000)
      constant := (61460019512463246482805591175658033709970257) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (452386554587160370951/100000000000000000000)
  centralHi := (56548319323395046369/12500000000000000000)
  directionLo := (91007974182813614357/20000000000000000000)
  directionHi := (227519935457034035893/50000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree087.table
  base := (-362265159118886604817724410404588741133/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (10336)
      previous := (7004)
      next := (0)
      square := (162613165768009655803849612140000000000000)
      linear := (-10890418200213482349869576005566000000000000)
      constant := (181576654146629414380247103501666821561437689) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree087.table
  base := (-362297751191505221450328099401400818481/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (3400)
      previous := (2380)
      next := (0)
      square := (54204388589336551934616537380000000000000)
      linear := (-3704112448028373018871217707770000000000000)
      constant := (63027816123040658957475598876542995163458991) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91007974182813614357/20000000000000000000)
  centralHi := (227519935457034035893/50000000000000000000)
  directionLo := (7151215707940813003/1562500000000000000)
  directionHi := (457677805308212032193/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree088.table
  base := (-44733873549731205457852525756545287189/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3251250000000000000000000000000000000000000
      center := (7752)
      previous := (5253)
      next := (0)
      square := (121959874326007241852887209105000000000000)
      linear := (-8266338097654847024448043828000500000000000)
      constant := (139620754901105757611132126074650425708021411) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree088.table
  base := (-8948221440505110001405766807899205697/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 72250000000000000000000000000000000000000
      center := (170)
      previous := (119)
      next := (0)
      square := (2710219429466827596730826869000000000000)
      linear := (-187437567813920744258515683986500000000000)
      constant := (3230760629469484685251405506068517129553567) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7151215707940813003/1562500000000000000)
  centralHi := (457677805308212032193/100000000000000000000)
  directionLo := (460300622226378857319/100000000000000000000)
  directionHi := (11507515555659471433/2500000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree089.table
  base := (269147753222411887547672194043340607/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 3251250000000000000000000000000000000000000
      center := (7752)
      previous := (5253)
      next := (0)
      square := (121959874326007241852887209105000000000000)
      linear := (-8364862545149582286493905651826500000000000)
      constant := (143101558458557378499607662646219953831350456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree089.table
  base := (17174087634326259144535274694865310823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (6800)
      previous := (4760)
      next := (0)
      square := (108408777178673103869233074760000000000000)
      linear := (-7586780529056913502938819303380000000000000)
      constant := (132444417656172540973887480620246816074827847) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460300622226378857319/100000000000000000000)
  centralHi := (11507515555659471433/2500000000000000000)
  directionLo := (462908578633234497111/100000000000000000000)
  directionHi := (57863572329154312139/12500000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree090.table
  base := (400758415384320736121357865103804045183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (20672)
      previous := (14008)
      next := (0)
      square := (325226331536019311607699224280000000000000)
      linear := (-22569031980384846796106046601740000000000000)
      constant := (390999736232506928823653919912524998107173661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree090.table
  base := (40071282295163548016762656360216660787/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 289000000000000000000000000000000000000000
      center := (680)
      previous := (476)
      next := (0)
      square := (10840877717867310386923307476000000000000)
      linear := (-767605834555699723553701124730000000000000)
      constant := (13569760953074681319668464852788102614967443) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (462908578633234497111/100000000000000000000)
  centralHi := (57863572329154312139/12500000000000000000)
  directionLo := (465501924295154068357/100000000000000000000)
  directionHi := (232750962147577034179/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree091.table
  base := (198181839363910323830001405534030924319/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6502500000000000000000000000000000000000000
      center := (15504)
      previous := (10506)
      next := (0)
      square := (243919748652014483705774418210000000000000)
      linear := (-17123822880278105621171258598957000000000000)
      constant := (300381565228282414564260991492672614434153719) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree091.table
  base := (396343448317899537278561687595499723221/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (3400)
      previous := (2380)
      next := (0)
      square := (54204388589336551934616537380000000000000)
      linear := (-3882668081028540484067601595610000000000000)
      constant := (69495000335981040993991981568945099420010869) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (465501924295154068357/100000000000000000000)
  centralHi := (232750962147577034179/50000000000000000000)
  directionLo := (468080902059399613531/100000000000000000000)
  directionHi := (117020225514849903383/25000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree092.table
  base := (1193131811039174659215629137410536420993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (62016)
      previous := (42024)
      next := (0)
      square := (975678994608057934823097672840000000000000)
      linear := (-69283487101070304581051928986436000000000000)
      constant := (1230393623089223606747851987103278405231002793) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree092.table
  base := (1193095908562983559960454385426524505613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (6800)
      previous := (4760)
      next := (0)
      square := (108408777178673103869233074760000000000000)
      linear := (-7854613978557164700733395135140000000000000)
      constant := (142321590964182559471385531337628265582122157) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468080902059399613531/100000000000000000000)
  centralHi := (117020225514849903383/25000000000000000000)
  directionLo := (23532287405976451169/5000000000000000000)
  directionHi := (470645748119529023381/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree093.table
  base := (400492839459099623268104475024048266767/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2167500000000000000000000000000000000000000
      center := (5168)
      previous := (3502)
      next := (0)
      square := (81306582884004827901924806070000000000000)
      linear := (-5839306890085682223118235298087000000000000)
      constant := (104966774511484014612561498333055649847286989) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree093.table
  base := (320387900780525080310743391681032916027/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (1360)
      previous := (952)
      next := (0)
      square := (21681755435734620773846614952000000000000)
      linear := (-1588778359011449686666317415812000000000000)
      constant := (29138476060972442557065049053063818512731803) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23532287405976451169/5000000000000000000)
  centralHi := (470645748119529023381/100000000000000000000)
  directionLo := (236598346133928555157/50000000000000000000)
  directionHi := (94639338453571422063/20000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree094.table
  base := (1009622813143117164250935961899776906223/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (31008)
      previous := (21012)
      next := (0)
      square := (487839497304028967411548836420000000000000)
      linear := (-35429939130493034386892859083826000000000000)
      constant := (644574636546226499484711728093124519733086023) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree094.table
  base := (2019217367611807276483909051689651127593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (6800)
      previous := (4760)
      next := (0)
      square := (108408777178673103869233074760000000000000)
      linear := (-8033169611557332165929779022980000000000000)
      constant := (149102368602953638823498587330698309175874377) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (236598346133928555157/50000000000000000000)
  centralHi := (94639338453571422063/20000000000000000000)
  directionLo := (475733958135732586273/100000000000000000000)
  directionHi := (237866979067866293137/50000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree095.table
  base := (2444954285986549271711743570366868085457/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (62016)
      previous := (42024)
      next := (0)
      square := (975678994608057934823097672840000000000000)
      linear := (-71648073840943950870152612758260000000000000)
      constant := (1319037559093782129947154779565184223890273657) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree095.table
  base := (76404038112730414941887210056279634207/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 361250000000000000000000000000000000000000
      center := (850)
      previous := (595)
      next := (0)
      square := (13551097147334137983654134345000000000000)
      linear := (-1015305928507176987315996370862500000000000)
      constant := (19068944472189100691111885323762559257143292) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (475733958135732586273/100000000000000000000)
  centralHi := (237866979067866293137/50000000000000000000)
  directionLo := (478257763422342020319/100000000000000000000)
  directionHi := (2989111021389637627/625000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree096.table
  base := (719774260697345094153863688408681856561/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2167500000000000000000000000000000000000000
      center := (5168)
      previous := (3502)
      next := (0)
      square := (81306582884004827901924806070000000000000)
      linear := (-6036355785075152747209958945739000000000000)
      constant := (112438845948059726388430063377613527169638387) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree096.table
  base := (2879074810532117782565557520510775717349/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (6800)
      previous := (4760)
      next := (0)
      square := (108408777178673103869233074760000000000000)
      linear := (-8211725244557499631126162910820000000000000)
      constant := (156039941756475480476190983357987614182313861) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (478257763422342020319/100000000000000000000)
  centralHi := (2989111021389637627/625000000000000000)
  directionLo := (240384160056351660591/50000000000000000000)
  directionHi := (480768320112703321183/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree097.table
  base := (3321673634488297376020091372285597941551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (62016)
      previous := (42024)
      next := (0)
      square := (975678994608057934823097672840000000000000)
      linear := (-73224465000859715062886401939476000000000000)
      constant := (1379835049259257833986472629507256440245974151) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree097.table
  base := (1660826959020859211389749164368742290763/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (3400)
      previous := (2380)
      next := (0)
      square := (54204388589336551934616537380000000000000)
      linear := (-4150501530528791681862177427370000000000000)
      constant := (79783763237792077250664547660472566522030507) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (240384160056351660591/50000000000000000000)
  centralHi := (480768320112703321183/100000000000000000000)
  directionLo := (96653166937093308399/20000000000000000000)
  directionHi := (120816458671366635499/25000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree098.table
  base := (3772683827026205867803770211320653478161/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (62016)
      previous := (42024)
      next := (0)
      square := (975678994608057934823097672840000000000000)
      linear := (-74012660580817597159253296530084000000000000)
      constant := (1410744252132622979383171368250654619696696761) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree098.table
  base := (1886333171774071144299930742550482249131/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (3400)
      previous := (2380)
      next := (0)
      square := (54204388589336551934616537380000000000000)
      linear := (-4195140438778833548161273399330000000000000)
      constant := (81567154938723443046633359424417089369998859) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96653166937093308399/20000000000000000000)
  centralHi := (120816458671366635499/25000000000000000000)
  directionLo := (242875254155549253923/50000000000000000000)
  directionHi := (485750508311098507847/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree099.table
  base := (4232127411160581206454058076041990677497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (20672)
      previous := (14008)
      next := (0)
      square := (325226331536019311607699224280000000000000)
      linear := (-24933618720258493085206730373564000000000000)
      constant := (480664586484190782082759712674049205917389899) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree099.table
  base := (846422381872638775550911926780928969129/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (1360)
      previous := (952)
      next := (0)
      square := (21681755435734620773846614952000000000000)
      linear := (-1695911738811550165784147748516000000000000)
      constant := (33348058382142357350369444139171688472078281) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242875254155549253923/50000000000000000000)
  centralHi := (485750508311098507847/100000000000000000000)
  directionLo := (488222537040989622963/100000000000000000000)
  directionHi := (122055634260247405741/25000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree100.table
  base := (940000839906151697080960707985253845021/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (62016)
      previous := (42024)
      next := (0)
      square := (975678994608057934823097672840000000000000)
      linear := (-75589051740733361351987085711300000000000000)
      constant := (1473583570731780845159817378961348226254498105) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree100.table
  base := (4699990456192831762253171786367242832969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (6800)
      previous := (4760)
      next := (0)
      square := (108408777178673103869233074760000000000000)
      linear := (-8568836510557834561518930686500000000000000)
      constant := (170385472529342878504381369196260133178728041) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (488222537040989622963/100000000000000000000)
  centralHi := (122055634260247405741/25000000000000000000)
  directionLo := (490682111987985953227/100000000000000000000)
  directionHi := (122670527996996488307/25000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree101.table
  base := (1035262804815722748476303363053643260211/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (62016)
      previous := (42024)
      next := (0)
      square := (975678994608057934823097672840000000000000)
      linear := (-76377247320691243448353980301908000000000000)
      constant := (1505513685533129295691910143130435030599044055) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree101.table
  base := (2588150920469489804706115228508233172243/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (3400)
      previous := (2380)
      next := (0)
      square := (54204388589336551934616537380000000000000)
      linear := (-4329057163528959147058561315210000000000000)
      constant := (87034925845992408645361821123368879386778227) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (490682111987985953227/100000000000000000000)
  centralHi := (122670527996996488307/25000000000000000000)
  directionLo := (246564709749408528467/50000000000000000000)
  directionHi := (98625883899763411387/20000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree102.table
  base := (5661056733779868039995628633136249007603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 510000000000000000000000000000000000000000
      center := (1216)
      previous := (824)
      next := (0)
      square := (19130960678589371271041130840000000000000)
      linear := (-1513047900012727951857272056716000000000000)
      constant := (30152629479682422516243328663939548699387753) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree102.table
  base := (5661045934770902341591078511095945971963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (400)
      previous := (280)
      next := (0)
      square := (6376986892863123757013710280000000000000)
      linear := (-514552479032823648630312622020000000000000)
      constant := (10458437021259148274907993525608631081523371) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (246564709749408528467/50000000000000000000)
  centralHi := (98625883899763411387/20000000000000000000)
  directionLo := (99112928263771966123/20000000000000000000)
  directionHi := (61945580164857478827/12500000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree103.table
  base := (3077116096324213967326126313389058013733/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (31008)
      previous := (21012)
      next := (0)
      square := (487839497304028967411548836420000000000000)
      linear := (-38976819240303503820543884741562000000000000)
      constant := (785197412085051887011262967856435739893719533) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree103.table
  base := (1230844524286580587841877355920140109031/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (1360)
      previous := (952)
      next := (0)
      square := (21681755435734620773846614952000000000000)
      linear := (-1767333992011617151862701303652000000000000)
      constant := (36311241100801418442771879426448920491509959) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99112928263771966123/20000000000000000000)
  centralHi := (61945580164857478827/12500000000000000000)
  directionLo := (497987954749650646569/100000000000000000000)
  directionHi := (49798795474965064657/10000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree104.table
  base := (831980034747591208699261775865641464349/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3251250000000000000000000000000000000000000
      center := (7752)
      previous := (5253)
      next := (0)
      square := (121959874326007241852887209105000000000000)
      linear := (-9842729257570611217181833009216500000000000)
      constant := (200418230916609750430366617682451333448771749) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree104.table
  base := (3327915897879600645473055082094821926371/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (3400)
      previous := (2380)
      next := (0)
      square := (54204388589336551934616537380000000000000)
      linear := (-4462973888279084745955849231090000000000000)
      constant := (92679090044698310729911190902005403536721219) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (497987954749650646569/100000000000000000000)
  centralHi := (49798795474965064657/10000000000000000000)
  directionLo := (100079906559906420377/20000000000000000000)
  directionHi := (250199766399766050943/50000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree105.table
  base := (7165880878811056334975082233443392643269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (20672)
      previous := (14008)
      next := (0)
      square := (325226331536019311607699224280000000000000)
      linear := (-26510009880174257277940519554780000000000000)
      constant := (545545724221168135635707049355215421421714223) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree105.table
  base := (7165873362370455093504400121608715943257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (6800)
      previous := (4760)
      next := (0)
      square := (108408777178673103869233074760000000000000)
      linear := (-9015225593058253224509890406100000000000000)
      constant := (189199353090009478485672054721644918907601273) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100079906559906420377/20000000000000000000)
  centralHi := (250199766399766050943/50000000000000000000)
  directionLo := (502799544327796609557/100000000000000000000)
  directionHi := (251399772163898304779/50000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree106.table
  base := (7684353894552314125443797238227195047379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (62016)
      previous := (42024)
      next := (0)
      square := (975678994608057934823097672840000000000000)
      linear := (-80318225220480653930188453254948000000000000)
      constant := (1670268799900355953427371513494435334318232779) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree106.table
  base := (768434723452953678455814321185175002833/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 289000000000000000000000000000000000000000
      center := (680)
      previous := (476)
      next := (0)
      square := (10840877717867310386923307476000000000000)
      linear := (-910450340955833695710808235002000000000000)
      constant := (19307972448077863342589616910098515575818737) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (502799544327796609557/100000000000000000000)
  centralHi := (251399772163898304779/50000000000000000000)
  directionLo := (505188154182666689743/100000000000000000000)
  directionHi := (31574259636416668109/6250000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree107.table
  base := (8211259233799844481814568726843904868119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (62016)
      previous := (42024)
      next := (0)
      square := (975678994608057934823097672840000000000000)
      linear := (-81106420800438536026555347845556000000000000)
      constant := (1704240728805689126091242108789958596561977519) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree107.table
  base := (1026406666642118099359319495645806957339/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 361250000000000000000000000000000000000000
      center := (850)
      previous := (595)
      next := (0)
      square := (13551097147334137983654134345000000000000)
      linear := (-1149222653257302586213284286742500000000000)
      constant := (24624911779855541290873306314909138210670971) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (505188154182666689743/100000000000000000000)
  centralHi := (31574259636416668109/6250000000000000000)
  directionLo := (507565523333431026187/100000000000000000000)
  directionHi := (126891380833357756547/25000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree108.table
  base := (8746596813278564990693571201088381625297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (20672)
      previous := (14008)
      next := (0)
      square := (325226331536019311607699224280000000000000)
      linear := (-27298205460132139374307414145388000000000000)
      constant := (579517653054301811847165197943794826869132499) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree108.table
  base := (8746591585848650179462620079615363646431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (6800)
      previous := (4760)
      next := (0)
      square := (108408777178673103869233074760000000000000)
      linear := (-9283059042558504422304466237860000000000000)
      constant := (200958062343299144823840494687248840093818559) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (507565523333431026187/100000000000000000000)
  centralHi := (126891380833357756547/25000000000000000000)
  directionLo := (101986361799407202773/20000000000000000000)
  directionHi := (254965904498518006933/50000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree109.table
  base := (9290366556916118835138513283241654423943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (62016)
      previous := (42024)
      next := (0)
      square := (975678994608057934823097672840000000000000)
      linear := (-82682811960354300219289137026772000000000000)
      constant := (1773205490774140681697265068745265943156675743) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree109.table
  base := (9290361926301303133649680462488037445521/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (6800)
      previous := (4760)
      next := (0)
      square := (108408777178673103869233074760000000000000)
      linear := (-9372336859058588154902658181780000000000000)
      constant := (204956028774964068822907904283119042821755569) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101986361799407202773/20000000000000000000)
  centralHi := (254965904498518006933/50000000000000000000)
  directionLo := (4002243474682925977/781250000000000000)
  directionHi := (512287164759414525057/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree110.table
  base := (4921284197513405119246386200141197427817/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (31008)
      previous := (21012)
      next := (0)
      square := (487839497304028967411548836420000000000000)
      linear := (-41735503770156091157828015808690000000000000)
      constant := (904099161729071184921733329109587254509752017) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree110.table
  base := (2460641073357896251160926154601717277741/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 722500000000000000000000000000000000000000
      center := (1700)
      previous := (1190)
      next := (0)
      square := (27102194294668275967308268690000000000000)
      linear := (-2365403668889667971875212531425000000000000)
      constant := (52248298379047950808382945478929896293267149) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4002243474682925977/781250000000000000)
  centralHi := (512287164759414525057/100000000000000000000)
  directionLo := (12865793517295421447/2500000000000000000)
  directionHi := (514631740691816857881/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree111.table
  base := (10403202263592946784349544838337464895269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (20672)
      previous := (14008)
      next := (0)
      square := (325226331536019311607699224280000000000000)
      linear := (-28086401040090021470674308735996000000000000)
      constant := (614510485682800160668342088597775382064198223) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree111.table
  base := (10403198630878122588566383795444546229517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (6800)
      previous := (4760)
      next := (0)
      square := (108408777178673103869233074760000000000000)
      linear := (-9550892492058755620099042069620000000000000)
      constant := (213069556550693911199791296355743473860330413) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12865793517295421447/2500000000000000000)
  centralHi := (514631740691816857881/100000000000000000000)
  directionLo := (103393136692478641723/20000000000000000000)
  directionHi := (64620710432799151077/12500000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree112.table
  base := (2194453620726365908055290190573181003621/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (62016)
      previous := (42024)
      next := (0)
      square := (975678994608057934823097672840000000000000)
      linear := (-85047398700227946508389820798596000000000000)
      constant := (1879204891391501018258687272012269818952091105) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree112.table
  base := (5486132443227905583925981031695019622627/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (3400)
      previous := (2380)
      next := (0)
      square := (54204388589336551934616537380000000000000)
      linear := (-4820085154279419676348617006770000000000000)
      constant := (108592558931694448729154972069679860670939203) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103393136692478641723/20000000000000000000)
  centralHi := (64620710432799151077/12500000000000000000)
  directionLo := (103857827288652487949/20000000000000000000)
  directionHi := (259644568221631219873/50000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree113.table
  base := (11549765860638055638858050934924642628607/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (62016)
      previous := (42024)
      next := (0)
      square := (975678994608057934823097672840000000000000)
      linear := (-85835594280185828604756715389204000000000000)
      constant := (1915218626345675425746302117932944595477006807) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree113.table
  base := (11549763011693645794439404076692018789559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (6800)
      previous := (4760)
      next := (0)
      square := (108408777178673103869233074760000000000000)
      linear := (-9729448125058923085295425957460000000000000)
      constant := (221339877440268641579098086051703993430182551) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103857827288652487949/20000000000000000000)
  centralHi := (259644568221631219873/50000000000000000000)
  directionLo := (52160223981328831981/10000000000000000000)
  directionHi := (521602239813288319811/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree114.table
  base := (12135695484092049172073144307285936237881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (20672)
      previous := (14008)
      next := (0)
      square := (325226331536019311607699224280000000000000)
      linear := (-28874596620047903567041203326604000000000000)
      constant := (650524220593174095843702553704693706718242827) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree114.table
  base := (6067846480714129291806873632519543011489/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (3400)
      previous := (2380)
      next := (0)
      square := (54204388589336551934616537380000000000000)
      linear := (-4909362970779503408946808950690000000000000)
      constant := (112766917634140465121736548954978147930320321) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52160223981328831981/10000000000000000000)
  centralHi := (521602239813288319811/100000000000000000000)
  directionLo := (523905130656771715753/100000000000000000000)
  directionHi := (261952565328385857877/50000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree115.table
  base := (2546011385405367169016635515528037268269/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (62016)
      previous := (42024)
      next := (0)
      square := (975678994608057934823097672840000000000000)
      linear := (-87411985440101592797490504570420000000000000)
      constant := (1988266997570880503472228823922182124673838345) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree115.table
  base := (2546010938689264475669212792769030352109/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (1360)
      previous := (952)
      next := (0)
      square := (21681755435734620773846614952000000000000)
      linear := (-1981600751611818110098361969060000000000000)
      constant := (45953398267045222380610723923810249771759501) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (523905130656771715753/100000000000000000000)
  centralHi := (261952565328385857877/50000000000000000000)
  directionLo := (105239588611651071307/20000000000000000000)
  directionHi := (65774742882281919567/12500000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree116.table
  base := (6666425072823021594765677627149504019887/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (31008)
      previous := (21012)
      next := (0)
      square := (487839497304028967411548836420000000000000)
      linear := (-44100090510029737446928699580514000000000000)
      constant := (1012650816802917854389734790641683059955726087) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree116.table
  base := (3333212042042456209431445578500356438203/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 722500000000000000000000000000000000000000
      center := (1700)
      previous := (1190)
      next := (0)
      square := (27102194294668275967308268690000000000000)
      linear := (-2499320393639793570772500447305000000000000)
      constant := (58509836407416535247829123977926603010640667) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (105239588611651071307/20000000000000000000)
  centralHi := (65774742882281919567/12500000000000000000)
  directionLo := (528480808193626696851/100000000000000000000)
  directionHi := (132120202048406674213/25000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree117.table
  base := (3486018774746739350842221903732896959769/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2167500000000000000000000000000000000000000
      center := (5168)
      previous := (3502)
      next := (0)
      square := (81306582884004827901924806070000000000000)
      linear := (-7415698050001446415852024479303000000000000)
      constant := (171889714148153657071141752594154221664119723) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree117.table
  base := (111552586787031651898855621262855236369/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 578000000000000000000000000000000000000000
      center := (1360)
      previous := (952)
      next := (0)
      square := (21681755435734620773846614952000000000000)
      linear := (-2017311878211851603137638746628000000000000)
      constant := (47670179628168898514032259467372129082766025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (528480808193626696851/100000000000000000000)
  centralHi := (132120202048406674213/25000000000000000000)
  directionLo := (132688463604423508847/25000000000000000000)
  directionHi := (530753854417694035389/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree118.table
  base := (14563731748623214255503991900773297499337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (62016)
      previous := (42024)
      next := (0)
      square := (975678994608057934823097672840000000000000)
      linear := (-89776572179975239086591188342244000000000000)
      constant := (2100391805986958058329853446506088946795775537) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree118.table
  base := (14563730198968004420720244357532393735923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (6800)
      previous := (4760)
      next := (0)
      square := (108408777178673103869233074760000000000000)
      linear := (-10175837207559341748286385677060000000000000)
      constant := (242701648858615615609603937340166861789681747) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132688463604423508847/25000000000000000000)
  centralHi := (530753854417694035389/100000000000000000000)
  directionLo := (106603441469680266267/20000000000000000000)
  directionHi := (66627150918550166417/12500000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree119.table
  base := (474744376825073670014935716971108573729/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 191250000000000000000000000000000000000000
      center := (456)
      previous := (309)
      next := (0)
      square := (7174110254471014226640424065000000000000)
      linear := (-665917409999508243992338845094500000000000)
      constant := (15723877515729012429098740318001218447122148) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree119.table
  base := (15191818686730211443663594542577605493709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 170000000000000000000000000000000000000000
      center := (400)
      previous := (280)
      next := (0)
      square := (6376986892863123757013710280000000000000)
      linear := (-603830295532907381228504565940000000000000)
      constant := (14534799869022515134149086456003819293393053) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106603441469680266267/20000000000000000000)
  centralHi := (66627150918550166417/12500000000000000000)
  directionLo := (535270989947838068049/100000000000000000000)
  directionHi := (10705419798956761361/2000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree120.table
  base := (7914169997107037125241579360657828661241/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4335000000000000000000000000000000000000000
      center := (10336)
      previous := (7004)
      next := (0)
      square := (162613165768009655803849612140000000000000)
      linear := (-15225493889981833879887496253910000000000000)
      constant := (362807196357614309597236536753450337449295947) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree120.table
  base := (3957084695042014600006506144604134984669/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 722500000000000000000000000000000000000000
      center := (1700)
      previous := (1190)
      next := (0)
      square := (27102194294668275967308268690000000000000)
      linear := (-2588598210139877303370692391225000000000000)
      constant := (62880186219010783636705592936790595010569341) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (535270989947838068049/100000000000000000000)
  centralHi := (10705419798956761361/2000000000000000000)
  directionLo := (21500612904007679603/4000000000000000000)
  directionHi := (134378830650047997519/25000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree121.table
  base := (8236645761892712540246029592900701071761/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 13005000000000000000000000000000000000000000
      center := (31008)
      previous := (21012)
      next := (0)
      square := (487839497304028967411548836420000000000000)
      linear := (-46070579459924442687845936057034000000000000)
      constant := (1107789656961318322047574161307223923487650361) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree121.table
  base := (8236645224662931936694056966966144785433/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (3400)
      previous := (2380)
      next := (0)
      square := (54204388589336551934616537380000000000000)
      linear := (-5221835328529796473040480754410000000000000)
      constant := (127994545078969777739561215395983215842990137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21500612904007679603/4000000000000000000)
  centralHi := (134378830650047997519/25000000000000000000)
  directionLo := (10795006463735690971/2000000000000000000)
  directionHi := (539750323186784548551/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree122.table
  base := (17126674616499828560729093458084615771591/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (62016)
      previous := (42024)
      next := (0)
      square := (975678994608057934823097672840000000000000)
      linear := (-92929354499806767472058766704676000000000000)
      constant := (2254655749390364321749829781694559685621908191) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree122.table
  base := (8563336832820989012660691105737639439871/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (3400)
      previous := (2380)
      next := (0)
      square := (54204388589336551934616537380000000000000)
      linear := (-5266474236779838339339576726370000000000000)
      constant := (130248316805408851637064408025778177798122719) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10795006463735690971/2000000000000000000)
  centralHi := (539750323186784548551/100000000000000000000)
  directionLo := (54197610715832139323/10000000000000000000)
  directionHi := (541976107158321393231/100000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree123.table
  base := (17788489243236955456988655877430403528049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (20672)
      previous := (14008)
      next := (0)
      square := (325226331536019311607699224280000000000000)
      linear := (-31239183359921549856141887098428000000000000)
      constant := (764690828157708971403098272479155359858818483) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree123.table
  base := (4447122100454545665689168356895791019421/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 722500000000000000000000000000000000000000
      center := (1700)
      previous := (1190)
      next := (0)
      square := (27102194294668275967308268690000000000000)
      linear := (-2655556572514940102819336349165000000000000)
      constant := (66260843806697098218511135361677883604612669) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54197610715832139323/10000000000000000000)
  centralHi := (541976107158321393231/100000000000000000000)
  directionLo := (2125753076580012549/390625000000000000)
  directionHi := (108838557520896642509/20000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree124.table
  base := (4614683844057757107394341291548013307599/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6502500000000000000000000000000000000000000
      center := (15504)
      previous := (10506)
      next := (0)
      square := (243919748652014483705774418210000000000000)
      linear := (-23626436414930632916198138971473000000000000)
      constant := (583457379774676408653250236285001982613064999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree124.table
  base := (9229367315852101780925306995653094918097/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (3400)
      previous := (2380)
      next := (0)
      square := (54204388589336551934616537380000000000000)
      linear := (-5355752053279922071937768670290000000000000)
      constant := (134814657499147097514089436004823744431330033) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2125753076580012549/390625000000000000)
  centralHi := (108838557520896642509/20000000000000000000)
  directionLo := (109280095064195122891/20000000000000000000)
  directionHi := (68300059415121951807/12500000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree125.table
  base := (3827482597789065407972907817350055275771/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (62016)
      previous := (42024)
      next := (0)
      square := (975678994608057934823097672840000000000000)
      linear := (-95293941239680413761159450476500000000000000)
      constant := (2373926853198078473100069760302137468861401855) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree125.table
  base := (19137412330195498727519827487933742619047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (6800)
      previous := (4760)
      next := (0)
      square := (108408777178673103869233074760000000000000)
      linear := (-10800781923059927876473729284500000000000000)
      constant := (274254452918079897099952711956512851616904583) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109280095064195122891/20000000000000000000)
  centralHi := (68300059415121951807/12500000000000000000)
  directionLo := (27429963943707526563/5000000000000000000)
  directionHi := (548599278874150531261/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree126.table
  base := (19824522055960963087259157133174966379213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (20672)
      previous := (14008)
      next := (0)
      square := (325226331536019311607699224280000000000000)
      linear := (-32027378939879431952508781689036000000000000)
      constant := (804788162235043633820254672862643495850777671) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree126.table
  base := (9912260736571356059579329209166341768233/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (3400)
      previous := (2380)
      next := (0)
      square := (54204388589336551934616537380000000000000)
      linear := (-5445029869780005804535960614210000000000000)
      constant := (139459394489583167596815513424029072771019337) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27429963943707526563/5000000000000000000)
  centralHi := (548599278874150531261/100000000000000000000)
  directionLo := (550789304663305793637/100000000000000000000)
  directionHi := (275394652331652896819/50000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree127.table
  base := (20520062552878224884717872071914194387399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 26010000000000000000000000000000000000000000
      center := (62016)
      previous := (42024)
      next := (0)
      square := (975678994608057934823097672840000000000000)
      linear := (-96870332399596177953893239657716000000000000)
      constant := (2455142419556399269597083973842918419601624799) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree127.table
  base := (10260031018635690176268600191030130483547/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1445000000000000000000000000000000000000000
      center := (3400)
      previous := (2380)
      next := (0)
      square := (54204388589336551934616537380000000000000)
      linear := (-5489668778030047670835056586170000000000000)
      constant := (141811161587413594695585686867277707709745083) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (550789304663305793637/100000000000000000000)
  centralHi := (275394652331652896819/50000000000000000000)
  directionLo := (138242664245191007069/25000000000000000000)
  directionHi := (552970656980764028277/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree128.table
  base := (5306008614057248583950191664987426906349/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 6502500000000000000000000000000000000000000
      center := (15504)
      previous := (10506)
      next := (0)
      square := (243919748652014483705774418210000000000000)
      linear := (-24414631994888515012565033562081000000000000)
      constant := (624065162922710750585047350329502697383413749) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree128.table
  base := (21224034000110653438639411925710336458797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (6800)
      previous := (4760)
      next := (0)
      square := (108408777178673103869233074760000000000000)
      linear := (-11068615372560179074268305116260000000000000)
      constant := (288365055498568384045748116635970287236592333) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell020.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (138242664245191007069/25000000000000000000)
  centralHi := (552970656980764028277/100000000000000000000)
  directionLo := (55514343806982686611/10000000000000000000)
  directionHi := (555143438069826866111/100000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 103
  qDenominator := 255
  table := BinomialMassData.Q103_255.Degree129.table
  base := (21936437743398921086478328499609078711533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8670000000000000000000000000000000000000000
      center := (20672)
      previous := (14008)
      next := (0)
      square := (325226331536019311607699224280000000000000)
      linear := (-32815574519837314048875676279644000000000000)
      constant := (845906394349880724806416513088953871242899111) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q103_255.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 7
  qDenominator := 17
  table := BinomialMassData.Q7_17.Degree129.table
  base := (21936437339929942759899084805618508337573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2890000000000000000000000000000000000000000
      center := (6800)
      previous := (4760)
      next := (0)
      square := (108408777178673103869233074760000000000000)
      linear := (-11157893189060262806866497060180000000000000)
      constant := (293146985944109779046884621369883748909558597) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_17.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell020.Kernel129
