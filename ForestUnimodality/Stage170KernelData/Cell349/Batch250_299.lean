import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage170KernelData.Cell349.Parameters
import ForestUnimodality.BinomialMassData.Q1_4.Batch250_299
import ForestUnimodality.BinomialMassData.Q9_35.Batch250_299

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel250
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217058403186071245273/50000000000000000000)
  centralHi := (434116806372142490547/100000000000000000000)
  directionLo := (6796736896083765141/1562500000000000000)
  directionHi := (17399646453974438761/4000000000000000000)

def endpointA : IntegerEndpointWitness 250 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree250.table
  base := (3780620166284442057019809643163819351071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-66950192984862985159932868760000000000000)
      constant := (2085456369883962866590748848572655277404284) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 250 interval.damping) (curvature.centralUpper 250 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree250.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 250 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree250.table
  base := (472577520785540296522160003517478048243/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-4219086297973624083597343754050000000000000)
      constant := (135162582671728840831471261474394256974556280) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 250 interval.damping) (curvature.centralUpper 250 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree250.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 250 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 250 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel250

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel251
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6796736896083765141/1562500000000000000)
  centralHi := (17399646453974438761/4000000000000000000)
  directionLo := (435863762349410416613/100000000000000000000)
  directionHi := (217931881174705208307/50000000000000000000)

def endpointA : IntegerEndpointWitness 251 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree251.table
  base := (3947325246985424389432872800682433254669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-67220791790921879428621910000000000000000)
      constant := (2102894563303739903993970448547729733018676) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 251 interval.damping) (curvature.centralUpper 251 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree251.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 251 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree251.table
  base := (789465049397063885014910617017903403919/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-4236134022755334422524753352170000000000000)
      constant := (136290525172022879774503934429860931669800775) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 251 interval.damping) (curvature.centralUpper 251 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree251.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 251 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 251 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel251

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel252
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435863762349410416613/100000000000000000000)
  centralHi := (217931881174705208307/50000000000000000000)
  directionLo := (436734619885693118087/100000000000000000000)
  directionHi := (54591827485711639761/12500000000000000000)

def endpointA : IntegerEndpointWitness 252 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree252.table
  base := (4115185861823561281803542435611165857317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-67491390596980773697310951240000000000000)
      constant := (2120405028561580283204194734742444663429268) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 252 interval.damping) (curvature.centralUpper 252 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree252.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 252 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree252.table
  base := (4115185861823469228741620049477904736259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (78)
      previous := (27)
      next := (0)
      square := (676497015147235671722603100000000000000)
      linear := (-86799627500756015539840060210000000000000)
      constant := (2804553764874258678135264680831389523681295) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 252 interval.damping) (curvature.centralUpper 252 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree252.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 252 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 252 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel252

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel253
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (436734619885693118087/100000000000000000000)
  centralHi := (54591827485711639761/12500000000000000000)
  directionLo := (218801872183499830781/50000000000000000000)
  directionHi := (437603744366999661563/100000000000000000000)

def endpointA : IntegerEndpointWitness 253 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree253.table
  base := (2142101000865780144625196504795413518261/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-67761989403039667965999992480000000000000)
      constant := (2137987765621214834441896005003363308146088) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 253 interval.damping) (curvature.centralUpper 253 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree253.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 253 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree253.table
  base := (2142101000865739780238091527045275889673/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-4270229472318755100379572548410000000000000)
      constant := (138560410589954740599281303289558185185939770) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 253 interval.damping) (curvature.centralUpper 253 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree253.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 253 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 253 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel253

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel254
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (218801872183499830781/50000000000000000000)
  centralHi := (437603744366999661563/100000000000000000000)
  directionLo := (438471146098960451669/100000000000000000000)
  directionHi := (43847114609896045167/10000000000000000000)

def endpointA : IntegerEndpointWitness 254 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree254.table
  base := (4454373657729632724574710673552298981503/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-68032588209098562234689033720000000000000)
      constant := (2155642774446724402958279403934209195926012) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 254 interval.damping) (curvature.centralUpper 254 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree254.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 254 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree254.table
  base := (1113593414432390481999152455173625324471/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-4287277197100465439306982146530000000000000)
      constant := (139702353503171027705854936308154152817981580) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 254 interval.damping) (curvature.centralUpper 254 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree254.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 254 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 254 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel254

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel255
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438471146098960451669/100000000000000000000)
  centralHi := (43847114609896045167/10000000000000000000)
  directionLo := (878673670570942861/200000000000000000)
  directionHi := (439336835285471430501/100000000000000000000)

def endpointA : IntegerEndpointWitness 255 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree255.table
  base := (4625700820924317143699349561670839757761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-68303187015157456503378074960000000000000)
      constant := (2173370055002535142977036348071683359031044) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 255 interval.damping) (curvature.centralUpper 255 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree255.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 255 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree255.table
  base := (185028032836970202328917197959954404613/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-4304324921882175778234391744650000000000000)
      constant := (140848963216308638536444275668454720728254625) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 255 interval.damping) (curvature.centralUpper 255 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree255.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 255 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 255 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel255

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel256
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (878673670570942861/200000000000000000)
  centralHi := (439336835285471430501/100000000000000000000)
  directionLo := (440200822030094564299/100000000000000000000)
  directionHi := (4402008220300945643/1000000000000000000)

def endpointA : IntegerEndpointWitness 256 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree256.table
  base := (959636696501464614110931023274894068129/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-68573785821216350772067116200000000000000)
      constant := (2191169607253413892593888219185497881362580) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 256 interval.damping) (curvature.centralUpper 256 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree256.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 256 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree256.table
  base := (4798183482507268625095567050262119484577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-4321372646663886117161801342770000000000000)
      constant := (142000239727209541961164725155218219273721365) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 256 interval.damping) (curvature.centralUpper 256 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree256.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 256 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 256 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel256

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel257
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (440200822030094564299/100000000000000000000)
  centralHi := (4402008220300945643/1000000000000000000)
  directionLo := (55132889542179204951/12500000000000000000)
  directionHi := (441063116337433639609/100000000000000000000)

def endpointA : IntegerEndpointWitness 257 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree257.table
  base := (4971821633754394537870346739082269590839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-68844384627275245040756157440000000000000)
      constant := (2209041431164463627939753894881329078363356) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 257 interval.damping) (curvature.centralUpper 257 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree257.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 257 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree257.table
  base := (4971821633754346792940780749712727037421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-4338420371445596456089210940890000000000000)
      constant := (143156183033736295300276218376625618124168145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 257 interval.damping) (curvature.centralUpper 257 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree257.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 257 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 257 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel257

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel258
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55132889542179204951/12500000000000000000)
  centralHi := (441063116337433639609/100000000000000000000)
  directionLo := (441923728114485898847/100000000000000000000)
  directionHi := (13810116503577684339/3125000000000000000)

def endpointA : IntegerEndpointWitness 258 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree258.table
  base := (2573307633012096515408969509936032290729/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-69114983433334139309445198680000000000000)
      constant := (2226985526701118994955319433519488258325832) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 258 interval.damping) (curvature.centralUpper 258 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree258.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 258 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree258.table
  base := (257330763301207558118567939085260478921/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-4355468096227306795016620539010000000000000)
      constant := (144316793133771770645928888327593776346712900) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 258 interval.damping) (curvature.centralUpper 258 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree258.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 258 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 258 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel258

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel259
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (441923728114485898847/100000000000000000000)
  centralHi := (13810116503577684339/3125000000000000000)
  directionLo := (1729619793640507937/390625000000000000)
  directionHi := (442782667171970031873/100000000000000000000)

def endpointA : IntegerEndpointWitness 259 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree259.table
  base := (2661282185378599715269403432681652902457/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-69385582239393033578134239920000000000000)
      constant := (2245001893829141917165150334726453223219656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 259 interval.damping) (curvature.centralUpper 259 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree259.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 259 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree259.table
  base := (33266027317232266973726574209118992501/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (78)
      previous := (27)
      next := (0)
      square := (676497015147235671722603100000000000000)
      linear := (-89235016755286063958041431370000000000000)
      constant := (2969021837249365017118631182373295194000800) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 259 interval.damping) (curvature.centralUpper 259 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree259.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 259 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 259 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel259

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel260
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1729619793640507937/390625000000000000)
  centralHi := (442782667171970031873/100000000000000000000)
  directionLo := (443639943225631027071/100000000000000000000)
  directionHi := (3465937056450242399/781250000000000000)

def endpointA : IntegerEndpointWitness 260 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree260.table
  base := (1374917234868658641113957438536822106459/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-69656181045451927846823281160000000000000)
      constant := (2263090532514617277878938116416589153703344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 260 interval.damping) (curvature.centralUpper 260 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree260.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 260 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree260.table
  base := (1374917234868650592367739125864890836659/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-4389563545790727472871439735250000000000000)
      constant := (146652013706000340003410933839947593019925820) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 260 interval.damping) (curvature.centralUpper 260 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree260.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 260 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 260 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel260

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel261
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (443639943225631027071/100000000000000000000)
  centralHi := (3465937056450242399/781250000000000000)
  directionLo := (444495565897522372927/100000000000000000000)
  directionHi := (6945243217148787077/1562500000000000000)

def endpointA : IntegerEndpointWitness 261 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree261.table
  base := (1135585792755479595966167587788339658007/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-69926779851510822115512322400000000000000)
      constant := (2281251442723948675285730099600766793160140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 261 interval.damping) (curvature.centralUpper 261 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree261.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 261 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree261.table
  base := (5677928963777369748580596764603353439271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-4406611270572437811798849333370000000000000)
      constant := (147826624174058353547893261441321821592621395) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 261 interval.damping) (curvature.centralUpper 261 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree261.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 261 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 261 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel261

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel262
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444495565897522372927/100000000000000000000)
  centralHi := (6945243217148787077/1562500000000000000)
  directionLo := (44534954471726608873/10000000000000000000)
  directionHi := (445349544717266088731/100000000000000000000)

def endpointA : IntegerEndpointWitness 262 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree262.table
  base := (5857344435345024566345301824305572805021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-70197378657569716384201363640000000000000)
      constant := (2299484624423854248944252165897222291220084) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 262 interval.damping) (curvature.centralUpper 262 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree262.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 262 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree262.table
  base := (366084027209062488197452458833914968257/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-4423658995354148150726258931490000000000000)
      constant := (149005901427354412536978257078104946675567440) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 262 interval.damping) (curvature.centralUpper 262 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree262.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 262 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 262 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel262

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel263
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44534954471726608873/10000000000000000000)
  centralHi := (445349544717266088731/100000000000000000000)
  directionLo := (89240377824658210237/20000000000000000000)
  directionHi := (223100944561645525593/50000000000000000000)

def endpointA : IntegerEndpointWitness 263 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree263.table
  base := (603791534593465866249991625649809192643/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-70467977463628610652890404880000000000000)
      constant := (2317790077581362576208507094690992367705720) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 263 interval.damping) (curvature.centralUpper 263 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree263.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 263 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree263.table
  base := (1207583069186927391132798920265591410733/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-4440706720135858489653668529610000000000000)
      constant := (150189845463869017348287912790371349478147925) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 263 interval.damping) (curvature.centralUpper 263 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree263.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 263 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 263 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel263

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel264
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (89240377824658210237/20000000000000000000)
  centralHi := (223100944561645525593/50000000000000000000)
  directionLo := (447052608464050072107/100000000000000000000)
  directionHi := (111763152116012518027/25000000000000000000)

def endpointA : IntegerEndpointWitness 264 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree264.table
  base := (6219641687380045289431737528669682420477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-70738576269687504921579446120000000000000)
      constant := (2336167802163808637163043111154678729681908) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 264 interval.damping) (curvature.centralUpper 264 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree264.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 264 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree264.table
  base := (1554910421845006563955665320323126238623/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-4457754444917568828581078127730000000000000)
      constant := (151378456281601435524885539268620663713850540) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 264 interval.damping) (curvature.centralUpper 264 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree264.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 264 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 264 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel264

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel265
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (447052608464050072107/100000000000000000000)
  centralHi := (111763152116012518027/25000000000000000000)
  directionLo := (223950855999608085589/50000000000000000000)
  directionHi := (447901711999216171179/100000000000000000000)

def endpointA : IntegerEndpointWitness 265 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree265.table
  base := (3201261725795269082158480920419004587211/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-71009175075746399190268487360000000000000)
      constant := (2354617798138829846676565000088352036697688) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 265 interval.damping) (curvature.centralUpper 265 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree265.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 265 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree265.table
  base := (6402523451590521474940643942307237797523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-4474802169699279167508487725850000000000000)
      constant := (152571733878569458738780960630315273260393135) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 265 interval.damping) (curvature.centralUpper 265 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree265.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 265 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 265 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel265

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel266
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223950855999608085589/50000000000000000000)
  centralHi := (447901711999216171179/100000000000000000000)
  directionLo := (448749208900858476759/100000000000000000000)
  directionHi := (11218730222521461919/2500000000000000000)

def endpointA : IntegerEndpointWitness 266 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree266.table
  base := (6586560630550124153781416450810321260917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-71279773881805293458957528600000000000000)
      constant := (2373140065474362152215576070523241285043668) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 266 interval.damping) (curvature.centralUpper 266 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree266.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 266 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree266.table
  base := (411660039409381845006543511754546905969/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (78)
      previous := (27)
      next := (0)
      square := (676497015147235671722603100000000000000)
      linear := (-91670406009816112376242802530000000000000)
      constant := (3138156699036921709841029214456363752477520) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 266 interval.damping) (curvature.centralUpper 266 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree266.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 266 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 266 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel266

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel267
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (448749208900858476759/100000000000000000000)
  centralHi := (11218730222521461919/2500000000000000000)
  directionLo := (7024923566478096519/1562500000000000000)
  directionHi := (449595108254598177217/100000000000000000000)

def endpointA : IntegerEndpointWitness 267 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree267.table
  base := (6771753216316463835897132149073436929829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-71550372687864187727646569840000000000000)
      constant := (2391734604138636196092364445621293747719316) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 267 interval.damping) (curvature.centralUpper 267 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree267.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 267 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree267.table
  base := (1692938304079112751218861307676973147351/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-4508897619262699845363306922090000000000000)
      constant := (154972289402374677505496305569729433684403980) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 267 interval.damping) (curvature.centralUpper 267 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree267.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 267 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 267 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel267

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel268
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7024923566478096519/1562500000000000000)
  centralHi := (449595108254598177217/100000000000000000000)
  directionLo := (225219709530372467419/50000000000000000000)
  directionHi := (450439419060744934839/100000000000000000000)

def endpointA : IntegerEndpointWitness 268 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree268.table
  base := (6958101201019947847141519469459327355757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-71820971493923081996335611080000000000000)
      constant := (2410401414100173540852839767517837309423028) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 268 interval.damping) (curvature.centralUpper 268 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree268.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 268 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree268.table
  base := (6958101201019936596857144015936899412713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-4525945344044410184290716520210000000000000)
      constant := (156179567325337945622201624786120540356114685) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 268 interval.damping) (curvature.centralUpper 268 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree268.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 268 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 268 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel268

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel269
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (225219709530372467419/50000000000000000000)
  centralHi := (450439419060744934839/100000000000000000000)
  directionLo := (14102567194856692639/3125000000000000000)
  directionHi := (451282150235414164449/100000000000000000000)

def endpointA : IntegerEndpointWitness 269 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree269.table
  base := (7145604576862768698386980813633683989087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-72091570299981976265024652320000000000000)
      constant := (2429140495327782956540491645819534735956348) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 269 interval.damping) (curvature.centralUpper 269 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree269.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 269 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree269.table
  base := (7145604576862758834222947100414314176703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-4542993068826120523218126118330000000000000)
      constant := (157391512019788505304178812023915506973292235) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 269 interval.damping) (curvature.centralUpper 269 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree269.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 269 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 269 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel269

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel270
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14102567194856692639/3125000000000000000)
  centralHi := (451282150235414164449/100000000000000000000)
  directionLo := (452123310611625569043/100000000000000000000)
  directionHi := (113030827652906392261/25000000000000000000)

def endpointA : IntegerEndpointWitness 270 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree270.table
  base := (7334263336118007751408318873861763373237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-72362169106040870533713693560000000000000)
      constant := (2447951847790556768602419291295447053492948) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 270 interval.damping) (curvature.centralUpper 270 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree270.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 270 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree270.table
  base := (1466852667223599820538450684460043051493/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-4560040793607830862145535716450000000000000)
      constant := (158608123483833261490929120022963552738078925) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 270 interval.damping) (curvature.centralUpper 270 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree270.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 270 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 270 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel270

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel271
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (452123310611625569043/100000000000000000000)
  centralHi := (113030827652906392261/25000000000000000000)
  directionLo := (113240727235095828831/25000000000000000000)
  directionHi := (18118516357615332613/4000000000000000000)

def endpointA : IntegerEndpointWitness 271 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree271.table
  base := (940509683891092131828865905447152306007/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-72632767912099764802402734800000000000000)
      constant := (2466835471457867265232324278319308873792224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 271 interval.damping) (curvature.centralUpper 271 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree271.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 271 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree271.table
  base := (7524077471128729471691160072001284256383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-4577088518389541201072945314570000000000000)
      constant := (159829401715596266839461942570414314642813835) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 271 interval.damping) (curvature.centralUpper 271 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree271.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 271 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 271 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel271

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel272
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113240727235095828831/25000000000000000000)
  centralHi := (18118516357615332613/4000000000000000000)
  directionLo := (113450238472934555699/25000000000000000000)
  directionHi := (453800953891738222797/100000000000000000000)

def endpointA : IntegerEndpointWitness 272 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree272.table
  base := (7715046974307135743912388615514528407787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-72903366718158659071091776040000000000000)
      constant := (2485791366299363162973636937662058113631148) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 272 interval.damping) (curvature.centralUpper 272 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree272.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 272 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree272.table
  base := (1928761743576782273873930927992702372473/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-4594136243171251540000354912690000000000000)
      constant := (161055346713218505242574913548568848325023540) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 272 interval.damping) (curvature.centralUpper 272 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree272.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 272 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 272 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel272

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel273
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113450238472934555699/25000000000000000000)
  centralHi := (453800953891738222797/100000000000000000000)
  directionLo := (227318727027916165559/50000000000000000000)
  directionHi := (454637454055832331119/100000000000000000000)

def endpointA : IntegerEndpointWitness 273 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree273.table
  base := (7907171838133620720961437104623086149537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-73173965524217553339780817280000000000000)
      constant := (2504819532284966129433192205783492344598148) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 273 interval.damping) (curvature.centralUpper 273 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree273.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 273 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree273.table
  base := (3953585919066807445984095611773299144539/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (78)
      previous := (27)
      next := (0)
      square := (676497015147235671722603100000000000000)
      linear := (-94105795264346160794444173690000000000000)
      constant := (3311958336221585282553964968231732991445390) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 273 interval.damping) (curvature.centralUpper 273 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree273.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 273 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 273 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel273

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel274
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (227318727027916165559/50000000000000000000)
  centralHi := (454637454055832331119/100000000000000000000)
  directionLo := (18218896717757048069/4000000000000000000)
  directionHi := (227736208971963100863/50000000000000000000)

def endpointA : IntegerEndpointWitness 274 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree274.table
  base := (4050226027577995664357751782642184436169/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-73444564330276447608469858520000000000000)
      constant := (2523919969384867361982739806101137475489352) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 274 interval.damping) (curvature.centralUpper 274 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree274.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 274 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree274.table
  base := (8100452055155986218212863283356445390931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-4628231692734672217855174108930000000000000)
      constant := (163521236998687998489660605920546329120778095) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 274 interval.damping) (curvature.centralUpper 274 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree274.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 274 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 274 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel274

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel275
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18218896717757048069/4000000000000000000)
  centralHi := (227736208971963100863/50000000000000000000)
  directionLo := (11407646349735232531/2500000000000000000)
  directionHi := (456305853989409301241/100000000000000000000)

def endpointA : IntegerEndpointWitness 275 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree275.table
  base := (1036860952248573468682205912066827994487/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-73715163136335341877158899760000000000000)
      constant := (2543092677569524221351411975811138495823584) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 275 interval.damping) (curvature.centralUpper 275 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree275.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 275 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree275.table
  base := (4147443808994291634468585965672804077591/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-4645279417516382556782583707050000000000000)
      constant := (164761182282899977523827201829929673998019590) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 275 interval.damping) (curvature.centralUpper 275 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree275.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 275 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 275 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel275

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel276
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11407646349735232531/2500000000000000000)
  centralHi := (456305853989409301241/100000000000000000000)
  directionLo := (28571110659299612873/6250000000000000000)
  directionHi := (457137770548793805969/100000000000000000000)

def endpointA : IntegerEndpointWitness 276 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree276.table
  base := (4245239259655731428892111010052780380787/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-73985761942394236145847941000000000000000)
      constant := (2562337656809656919037594129800422243046296) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 276 interval.damping) (curvature.centralUpper 276 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree276.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 276 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree276.table
  base := (4245239259655729464816756093292392767807/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-4662327142298092895709993305170000000000000)
      constant := (166005794325700228904589707951177272456225430) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 276 interval.damping) (curvature.centralUpper 276 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree276.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 276 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 276 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel276

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel277
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28571110659299612873/6250000000000000000)
  centralHi := (457137770548793805969/100000000000000000000)
  directionLo := (91593635180538431753/20000000000000000000)
  directionHi := (228984087951346079383/50000000000000000000)

def endpointA : IntegerEndpointWitness 277 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree277.table
  base := (8687224751869567266700173336444800823429/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-74256360748453130414536982240000000000000)
      constant := (2581654907076245257493306050470779203293716) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 277 interval.damping) (curvature.centralUpper 277 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree277.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 277 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree277.table
  base := (1737444950373912764572480654343385727513/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-4679374867079803234637402903290000000000000)
      constant := (167255073125311265534475451493836647516203425) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 277 interval.damping) (curvature.centralUpper 277 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree277.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 277 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 277 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel277

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel278
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91593635180538431753/20000000000000000000)
  centralHi := (228984087951346079383/50000000000000000000)
  directionLo := (229398539128389350873/50000000000000000000)
  directionHi := (458797078256778701747/100000000000000000000)

def endpointA : IntegerEndpointWitness 278 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree278.table
  base := (4442563154235973655538725295904409270607/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-74526959554512024683226023480000000000000)
      constant := (2601044428340525422058035535207235274164856) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 278 interval.damping) (curvature.centralUpper 278 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree278.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 278 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree278.table
  base := (1777025261694388858375137966793732288139/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-4696422591861513573564812501410000000000000)
      constant := (168509018679971303767581134396478322052970275) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 278 interval.damping) (curvature.centralUpper 278 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree278.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 278 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 278 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel278

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel279
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229398539128389350873/50000000000000000000)
  centralHi := (458797078256778701747/100000000000000000000)
  directionLo := (229812242871367850381/50000000000000000000)
  directionHi := (459624485742735700763/100000000000000000000)

def endpointA : IntegerEndpointWitness 279 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree279.table
  base := (9084183181990955718591969038774160003451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-74797558360570918951915064720000000000000)
      constant := (2620506220573986823642486245020096640013804) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 279 interval.damping) (curvature.centralUpper 279 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree279.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 279 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree279.table
  base := (4542091590995476535849025409093444090169/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-4713470316643223912492222099530000000000000)
      constant := (169767630987934070023987803000589787604182810) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 279 interval.damping) (curvature.centralUpper 279 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree279.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 279 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 279 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel279

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel280
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229812242871367850381/50000000000000000000)
  centralHi := (459624485742735700763/100000000000000000000)
  directionLo := (23022520320959203507/5000000000000000000)
  directionHi := (460450406419184070141/100000000000000000000)

def endpointA : IntegerEndpointWitness 280 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree280.table
  base := (4642197682680737361940920168348571266939/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-75068157166629813220604105960000000000000)
      constant := (2640040283748368991185210626546788570135512) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 280 interval.damping) (curvature.centralUpper 280 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree280.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 280 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree280.table
  base := (9284395365361472403412018593596062603373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (78)
      previous := (27)
      next := (0)
      square := (676497015147235671722603100000000000000)
      linear := (-96541184518876209212645544850000000000000)
      constant := (3490426735662624703117564851767980313016865) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 280 interval.damping) (curvature.centralUpper 280 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree280.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 280 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 280 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel280

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel281
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (23022520320959203507/5000000000000000000)
  centralHi := (460450406419184070141/100000000000000000000)
  directionLo := (57659356034074887381/12500000000000000000)
  directionHi := (461274848272599099049/100000000000000000000)

def endpointA : IntegerEndpointWitness 281 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree281.table
  base := (4742881425790075693623879375660050750771/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-75338755972688707489293147200000000000000)
      constant := (2659646617835658512927411456850280406006168) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 281 interval.damping) (curvature.centralUpper 281 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree281.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 281 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree281.table
  base := (2371440712895037338242393891150520418437/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-4747565766206644590347041295770000000000000)
      constant := (172298855856859103585057994293681510010068260) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 281 interval.damping) (curvature.centralUpper 281 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree281.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 281 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 281 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel281

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel282
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57659356034074887381/12500000000000000000)
  centralHi := (461274848272599099049/100000000000000000000)
  directionLo := (462097819218211473823/100000000000000000000)
  directionHi := (14440556850569108557/3125000000000000000)

def endpointA : IntegerEndpointWitness 282 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree282.table
  base := (9688285633704644884571684232624211776271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-75609354778747601757982188440000000000000)
      constant := (2679325222808086025572616575730496847105084) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 282 interval.damping) (curvature.centralUpper 282 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree282.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 282 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree282.table
  base := (4844142816852321550604190980324550297727/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-4764613490988354929274450893890000000000000)
      constant := (173571468414404675920184979427955029645886230) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 282 interval.damping) (curvature.centralUpper 282 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree282.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 282 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 282 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel282

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel283
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (462097819218211473823/100000000000000000000)
  centralHi := (14440556850569108557/3125000000000000000)
  directionLo := (462919327100893883819/100000000000000000000)
  directionHi := (23145966355044694191/5000000000000000000)

def endpointA : IntegerEndpointWitness 283 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree283.table
  base := (9891963704852885540398584947249902056707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-75879953584806496026671229680000000000000)
      constant := (2699076098638123250419005855853999608226828) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 283 interval.damping) (curvature.centralUpper 283 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree283.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 283 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree283.table
  base := (9891963704852883977019075302137287291761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-4781661215770065268201860492010000000000000)
      constant := (174848747718419220388719839331949635386481445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 283 interval.damping) (curvature.centralUpper 283 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree283.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 283 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 283 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel283

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel284
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (462919327100893883819/100000000000000000000)
  centralHi := (23145966355044694191/5000000000000000000)
  directionLo := (92747875939206698339/20000000000000000000)
  directionHi := (28983711231002093231/6250000000000000000)

def endpointA : IntegerEndpointWitness 284 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree284.table
  base := (10096797058202345381224506518073267641377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-76150552390865390295360270920000000000000)
      constant := (2718899245298480075572563479712293070565508) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 284 interval.damping) (curvature.centralUpper 284 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree284.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 284 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree284.table
  base := (403871882328093760428335234809590365233/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-4798708940551775607129270090130000000000000)
      constant := (176130693767231217638087721699552740987052125) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 284 interval.damping) (curvature.centralUpper 284 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree284.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 284 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 284 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel284

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel285
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92747875939206698339/20000000000000000000)
  centralHi := (28983711231002093231/6250000000000000000)
  directionLo := (3716463877683124341/800000000000000000)
  directionHi := (232278992355195271313/50000000000000000000)

def endpointA : IntegerEndpointWitness 285 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree285.table
  base := (2575696421747329997755811124253067251043/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-76421151196924284564049312160000000000000)
      constant := (2738794662762101683369184629513049076016688) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 285 interval.damping) (curvature.centralUpper 285 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree285.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 285 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree285.table
  base := (2575696421747329697397900291611065099843/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-4815756665333485946056679688250000000000000)
      constant := (177417306559183560087180875643628843797846140) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 285 interval.damping) (curvature.centralUpper 285 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree285.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 285 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 285 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel285

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel286
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3716463877683124341/800000000000000000)
  centralHi := (232278992355195271313/50000000000000000000)
  directionLo := (465375149782943380639/100000000000000000000)
  directionHi := (2908594686143396129/625000000000000000)

def endpointA : IntegerEndpointWitness 286 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree286.table
  base := (10509929584508221455900272488177751118899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-76691750002983178832738353400000000000000)
      constant := (2758762351002165722153291199672711004475596) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 286 interval.damping) (curvature.centralUpper 286 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree286.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 286 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree286.table
  base := (5254964792254110201352134881882978879549/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-4832804390115196284984089286370000000000000)
      constant := (178708586092633378697813006889566659650979010) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 286 interval.damping) (curvature.centralUpper 286 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree286.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 286 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 286 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel286

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel287
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (465375149782943380639/100000000000000000000)
  centralHi := (2908594686143396129/625000000000000000)
  directionLo := (116547720621430033543/25000000000000000000)
  directionHi := (466190882485720134173/100000000000000000000)

def endpointA : IntegerEndpointWitness 287 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree287.table
  base := (10718228744110882189472280677806621517573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-76962348809042073101427394640000000000000)
      constant := (2778802309992079521579349950936226486070292) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 287 interval.damping) (curvature.centralUpper 287 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree287.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 287 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree287.table
  base := (10718228744110881266232318245088417532509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (78)
      previous := (27)
      next := (0)
      square := (676497015147235671722603100000000000000)
      linear := (-98976573773406257630846916010000000000000)
      constant := (3673561885019425967590809564799442087662545) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 287 interval.damping) (curvature.centralUpper 287 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree287.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 287 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 287 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel287

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel288
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116547720621430033543/25000000000000000000)
  centralHi := (466190882485720134173/100000000000000000000)
  directionLo := (467005190324617326979/100000000000000000000)
  directionHi := (23350259516230866349/5000000000000000000)

def endpointA : IntegerEndpointWitness 288 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree288.table
  base := (273192078980146735880234763449485399449/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-77232947615100967370116435880000000000000)
      constant := (2798914539705477350621241369191917663911840) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 288 interval.damping) (curvature.centralUpper 288 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree288.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 288 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree288.table
  base := (1365960394900733578237336742275425271183/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-4866899839678616962838908482610000000000000)
      constant := (181305145377524140204792983095755833531518680) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 288 interval.damping) (curvature.centralUpper 288 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree288.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 288 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 288 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel288

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel289
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (467005190324617326979/100000000000000000000)
  centralHi := (23350259516230866349/5000000000000000000)
  directionLo := (233909040370102832371/50000000000000000000)
  directionHi := (467818080740205664743/100000000000000000000)

def endpointA : IntegerEndpointWitness 289 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree289.table
  base := (5569146411628905123217306751512328463499/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-77503546421159861638805477120000000000000)
      constant := (2819099040116217717492257500177098627707992) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 289 interval.damping) (curvature.centralUpper 289 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree289.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 289 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree289.table
  base := (5569146411628904768500880576681731675029/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-4883947564460327301766318080730000000000000)
      constant := (182610425125749015704891049407328048520764210) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 289 interval.damping) (curvature.centralUpper 289 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree289.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 289 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 289 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel289

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel290
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233909040370102832371/50000000000000000000)
  centralHi := (467818080740205664743/100000000000000000000)
  directionLo := (468629561108523242083/100000000000000000000)
  directionHi := (117157390277130810521/25000000000000000000)

def endpointA : IntegerEndpointWitness 290 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree290.table
  base := (227001154595734534981675205977228937807/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-77774145227218755907494518360000000000000)
      constant := (2839355811198380710696141586795445787561400) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 290 interval.damping) (curvature.centralUpper 290 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree290.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 290 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree290.table
  base := (11350057729786726127209363602675215779601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-4900995289242037640693727678850000000000000)
      constant := (183920371609038904333522489319355427866002245) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 290 interval.damping) (curvature.centralUpper 290 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree290.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 290 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 290 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel290

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel291
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (468629561108523242083/100000000000000000000)
  centralHi := (117157390277130810521/25000000000000000000)
  directionLo := (469439638741856409171/100000000000000000000)
  directionHi := (117359909685464102293/25000000000000000000)

def endpointA : IntegerEndpointWitness 291 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree291.table
  base := (11562977872367381496570563642802066009537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-78044744033277650176183559600000000000000)
      constant := (2859684852926265380446548559916208264038148) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 291 interval.damping) (curvature.centralUpper 291 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree291.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 291 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree291.table
  base := (2890744468091845237863474832323371694813/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-4918043014023747979621137276970000000000000)
      constant := (185234984825819622916645740352410904260916740) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 291 interval.damping) (curvature.centralUpper 291 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree291.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 291 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 291 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel291

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel292
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (469439638741856409171/100000000000000000000)
  centralHi := (117359909685464102293/25000000000000000000)
  directionLo := (470248320889508531773/100000000000000000000)
  directionHi := (235124160444754265887/50000000000000000000)

def endpointA : IntegerEndpointWitness 292 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree292.table
  base := (11777053244628632730279039880360447330071/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-78315342839336544444872600840000000000000)
      constant := (2880086165274387159709014484921441789320284) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 292 interval.damping) (curvature.centralUpper 292 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree292.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 292 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree292.table
  base := (11777053244628632252450950042253536967699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-4935090738805458318548546875090000000000000)
      constant := (186554264774530241723726120025208116557086255) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 292 interval.damping) (curvature.centralUpper 292 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree292.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 292 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 292 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel292

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel293
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (470248320889508531773/100000000000000000000)
  centralHi := (235124160444754265887/50000000000000000000)
  directionLo := (235527807369278436683/50000000000000000000)
  directionHi := (471055614738556873367/100000000000000000000)

def endpointA : IntegerEndpointWitness 293 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree293.table
  base := (11992283840252799363247211364117872454587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-78585941645395438713561642080000000000000)
      constant := (2900559748217475324135691451221471489818348) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 293 interval.damping) (curvature.centralUpper 293 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree293.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 293 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree293.table
  base := (5996141920126399472203019789380012117411/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-4952138463587168657475956473210000000000000)
      constant := (187878211453622928888743981677862205937531390) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 293 interval.damping) (curvature.centralUpper 293 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree293.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 293 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 293 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel293

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel294
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235527807369278436683/50000000000000000000)
  centralHi := (471055614738556873367/100000000000000000000)
  directionLo := (29491345463412363929/6250000000000000000)
  directionHi := (94372305482919564573/20000000000000000000)

def endpointA : IntegerEndpointWitness 294 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree294.table
  base := (12208669652975035508580883172317634458579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-78856540451454332982250683320000000000000)
      constant := (2921105601730470490179002679129270537834316) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 294 interval.damping) (curvature.centralUpper 294 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree294.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 294 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree294.table
  base := (6104334826487517570724306188651384341613/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (78)
      previous := (27)
      next := (0)
      square := (676497015147235671722603100000000000000)
      linear := (-101411963027936306049048287170000000000000)
      constant := (3861363772684955044278796718322513843416130) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 294 interval.damping) (curvature.centralUpper 294 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree294.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 294 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 294 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel294

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel295
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29491345463412363929/6250000000000000000)
  centralHi := (94372305482919564573/20000000000000000000)
  directionLo := (94533213196496137303/20000000000000000000)
  directionHi := (118166516495620171629/25000000000000000000)

def endpointA : IntegerEndpointWitness 295 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree295.table
  base := (12426210676582714377950357269237485264519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-79127139257513227250939724560000000000000)
      constant := (2941723725788522150685629376501949941058076) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 295 interval.damping) (curvature.centralUpper 295 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree295.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 295 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree295.table
  base := (776638167286419628509153971606724800187/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-4986233913150589335330775669450000000000000)
      constant := (190540104996827753003556402386448361216733040) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 295 interval.damping) (curvature.centralUpper 295 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree295.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 295 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 295 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel295

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel296
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94533213196496137303/20000000000000000000)
  centralHi := (118166516495620171629/25000000000000000000)
  directionLo := (473469237447030257763/100000000000000000000)
  directionHi := (118367309361757564441/25000000000000000000)

def endpointA : IntegerEndpointWitness 296 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree296.table
  base := (12644906904914821379347088265107699332073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-79397738063572121519628765800000000000000)
      constant := (2962414120366986247287537361780430797328292) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 296 interval.damping) (curvature.centralUpper 296 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree296.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 296 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree296.table
  base := (790306681557176318579870646910650490699/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-5003281637932299674258185267570000000000000)
      constant := (191878051857908347815580763874113749923540080) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 296 interval.damping) (curvature.centralUpper 296 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree296.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 296 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 296 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel296

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel297
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (473469237447030257763/100000000000000000000)
  centralHi := (118367309361757564441/25000000000000000000)
  directionLo := (474271048753758374089/100000000000000000000)
  directionHi := (47427104875375837409/10000000000000000000)

def endpointA : IntegerEndpointWitness 297 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree297.table
  base := (6432379165930678123436868214946955335579/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-79668336869631015788317807040000000000000)
      constant := (2983176785441422778921137276044575642684632) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 297 interval.damping) (curvature.centralUpper 297 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree297.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 297 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree297.table
  base := (321618958296533899990889222333499164313/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-5020329362714010013185594865690000000000000)
      constant := (193220665443307631540758299905654291810267400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 297 interval.damping) (curvature.centralUpper 297 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree297.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 297 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 297 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel297

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel298
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (474271048753758374089/100000000000000000000)
  centralHi := (47427104875375837409/10000000000000000000)
  directionLo := (47507150678956466531/10000000000000000000)
  directionHi := (475071506789564665311/100000000000000000000)

def endpointA : IntegerEndpointWitness 298 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree298.table
  base := (3271441237840686009741500714036303926519/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-79938935675689910057006848280000000000000)
      constant := (3004011720987593445820171923664580862824304) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 298 interval.damping) (curvature.centralUpper 298 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree298.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 298 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree298.table
  base := (13085764951362743822259936032498190945133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-5037377087495720352113004463810000000000000)
      constant := (194567945751541008318553946911398056781557585) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 298 interval.damping) (curvature.centralUpper 298 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree298.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 298 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 298 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel298

namespace ForestUnimodality.Stage170KernelData.Cell349.Kernel299
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47507150678956466531/10000000000000000000)
  centralHi := (475071506789564665311/100000000000000000000)
  directionLo := (475870618383426693333/100000000000000000000)
  directionHi := (237935309191713346667/50000000000000000000)

def endpointA : IntegerEndpointWitness 299 where
  qNumerator := 1
  qDenominator := 4
  table := BinomialMassData.Q1_4.Degree299.table
  base := (13307926757409254844922853745439572344569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 40000000000000000000000000000000000000000
      center := (63)
      previous := (21)
      next := (0)
      square := (541197612117788537378082480000000000000)
      linear := (-80209534481748804325695889520000000000000)
      constant := (3024918926981459328341837169446758289378276) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 299 interval.damping) (curvature.centralUpper 299 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q1_4.Degree299.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 299 where
  qNumerator := 9
  qDenominator := 35
  table := BinomialMassData.Q9_35.Degree299.table
  base := (6653963378704627327490144894667771809709/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (3822)
      previous := (1323)
      next := (0)
      square := (33148353742214547914407551900000000000000)
      linear := (-5054424812277430691040414061930000000000000)
      constant := (195919892781136094320975873106561208186757410) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 299 interval.damping) (curvature.centralUpper 299 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9_35.Degree299.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 299 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 299 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage170KernelData.Cell349.Kernel299
