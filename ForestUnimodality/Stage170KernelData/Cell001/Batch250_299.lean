import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage170KernelData.Cell001.Parameters
import ForestUnimodality.BinomialMassData.Q1_4.Batch250_299
import ForestUnimodality.BinomialMassData.Q9_35.Batch250_299

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel250
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
  base := (-2081945444693616632887966008945436605399/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-6236687339080373999183892980000000000000)
      constant := (190776304133748757431954681178554563394601) }

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
  base := (-4163890889388216836281928963433243015403/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-3144203545832491547996207057700000000000000)
      constant := (99016264330877609816523391148958855461226265) }

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
end ForestUnimodality.Stage170KernelData.Cell001.Kernel250

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel251
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
  base := (-31971729569602267084833778969534190879/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-6261894981846976367297064265000000000000)
      constant := (192374381676103747767223404989074811783744) }

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
  base := (-1023095346227488196091916439367415624719/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 612500000000000000000000000000000000000000
      center := (1092)
      previous := (378)
      next := (0)
      square := (6175872477817580187726964825000000000000)
      linear := (-789227049446714785381311346335000000000000)
      constant := (24960981774485032399473785951416983171943845) }

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
end ForestUnimodality.Stage170KernelData.Cell001.Kernel251

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel252
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
  base := (-1005056741306174200698113292243844351943/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-6287102624613578735410235550000000000000)
      constant := (193979083586753513847094952735512311296114) }

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
  base := (-4020226965225453295216890005647823597661/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (624)
      previous := (216)
      next := (0)
      square := (3529069987324331535843979900000000000000)
      linear := (-452801835677318105007754816140000000000000)
      constant := (14382144968532961246899615576378326174081865) }

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
end ForestUnimodality.Stage170KernelData.Cell001.Kernel252

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel253
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
  base := (-1973713820348337676803653159111238148291/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-6312310267380181103523406835000000000000)
      constant := (195590409860516744551554231459013761851709) }

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
  base := (-789485528139467756598168753353412124807/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-3182317501695594328583322040620000000000000)
      constant := (101509527373710565206260382531494070147111425) }

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
end ForestUnimodality.Stage170KernelData.Cell001.Kernel253

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel254
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
  base := (-1936991710793821747402739172126625010397/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-6337517910146783471636578120000000000000)
      constant := (197208360492262131052850143565373374989603) }

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
  base := (-1936991710794112650681190150177936572153/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2184)
      previous := (756)
      next := (0)
      square := (12351744955635160375453929650000000000000)
      linear := (-1597511076824980961056180184130000000000000)
      constant := (51173732438682649049317257623810405539822515) }

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
end ForestUnimodality.Stage170KernelData.Cell001.Kernel254

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel255
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
  base := (-3799894318061558921946449592665285291711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-12725451105826771679499498810000000000000)
      constant := (397665870953815389006405897763584714708289) }

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
  base := (-3799894318062069140635520347200692268447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-3207726805604329515641398695900000000000000)
      constant := (103188827288204758114295222101535830394230485) }

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
end ForestUnimodality.Stage170KernelData.Cell001.Kernel255

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel256
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
  base := (-3725160340185040859839566498180508732207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-12775866391359976415725841380000000000000)
      constant := (400928269618840250580415948381819491267793) }

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
  base := (-1862580170092744146418099376482940035307/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2184)
      previous := (756)
      next := (0)
      square := (12351744955635160375453929650000000000000)
      linear := (-1610215728779348554585218511770000000000000)
      constant := (52016807301881311922598074528025679691349785) }

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
end ForestUnimodality.Stage170KernelData.Cell001.Kernel256

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel257
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
  base := (-1824890748964334450484618873715279843359/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-6413140838446590575976091975000000000000)
      constant := (202101958484814133617623015149409720156641) }

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
  base := (-1824890748964530634493969885316596262909/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2184)
      previous := (756)
      next := (0)
      square := (12351744955635160375453929650000000000000)
      linear := (-1616568054756532351349737675590000000000000)
      constant := (52440913410798051778068266334593433915587295) }

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
end ForestUnimodality.Stage170KernelData.Cell001.Kernel257

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel258
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
  base := (-714751560233651933144332090398523551867/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-12876696962426385888178526520000000000000)
      constant := (407492812996303622350509946403007382240665) }

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
  base := (-1786878900584301870390052195548827946757/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2184)
      previous := (756)
      next := (0)
      square := (12351744955635160375453929650000000000000)
      linear := (-1622920380733716148114256839410000000000000)
      constant := (52866731969642811203776239749086537153044535) }

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
end ForestUnimodality.Stage170KernelData.Cell001.Kernel258

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel259
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
  base := (-3497089259686121745386358029168334613469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-12927112247959590624404869090000000000000)
      constant := (410794957689084007334918173277081665386531) }

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
  base := (-3497089259686423467284880187270482957989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (624)
      previous := (216)
      next := (0)
      square := (3529069987324331535843979900000000000000)
      linear := (-465506487631685698536793143780000000000000)
      constant := (15226932279204930714067329083949533096470385) }

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
end ForestUnimodality.Stage170KernelData.Cell001.Kernel259

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel260
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
  base := (-3419775883172289377578402010703609915533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-12977527533492795360631211660000000000000)
      constant := (414110351038279387950855639389296390084467) }

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
  base := (-3419775883172553956090543276107270268473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-3271250065376167483286590334100000000000000)
      constant := (107447012864668723119533877288953718784224115) }

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
end ForestUnimodality.Stage170KernelData.Cell001.Kernel260

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel261
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
  base := (-835454420306433823186991334132504850499/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-6513971409513000048428777115000000000000)
      constant := (208719496517145395733936085899859990299002) }

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
  base := (-1670908840612983648636665879028547631413/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2184)
      previous := (756)
      next := (0)
      square := (12351744955635160375453929650000000000000)
      linear := (-1641977358665267538407814330870000000000000)
      constant := (54154462333818249304335761133742005830303815) }

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
end ForestUnimodality.Stage170KernelData.Cell001.Kernel261

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel262
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
  base := (-40790183291944539496942433941244972123/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-6539179052279602416541948400000000000000)
      constant := (210390441833804557108553711899850201115080) }

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
  base := (-3263214663355766597971687643739092807673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-3296659369284902670344666989380000000000000)
      constant := (109174261361008111204635320230635922262120115) }

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
end ForestUnimodality.Stage170KernelData.Cell001.Kernel262

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel263
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
  base := (-3183966838982180048146312611418374781137/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-13128773390092409569310239370000000000000)
      constant := (424136022928813949129015772924831625218863) }

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
  base := (-636793367796471687001835030148590939951/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-3309364021239270263873705317020000000000000)
      constant := (110043022942475561296103497945099976098560025) }

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
end ForestUnimodality.Stage170KernelData.Cell001.Kernel263

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel264
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
  base := (-1552037108719224657334101745406979988997/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-6589594337812807152768290970000000000000)
      constant := (213752205404286216423424867354593020011003) }

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
  base := (-310407421743860573294235078191355779809/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2184)
      previous := (756)
      next := (0)
      square := (12351744955635160375453929650000000000000)
      linear := (-1661034336596818928701371822330000000000000)
      constant := (55457604704876148733279849533839589169733975) }

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
end ForestUnimodality.Stage170KernelData.Cell001.Kernel264

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel265
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
  base := (-755884201992706077936977879185951880417/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-6614801980579409520881462255000000000000)
      constant := (215443023648819056009091232494753096239166) }

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
  base := (-188971050498185091569252700421913309703/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 306250000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (3087936238908790093863482412500000000000)
      linear := (-416846665643500681366472746537500000000000)
      constant := (13973852595071617342192050071793262478245530) }

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
end ForestUnimodality.Stage170KernelData.Cell001.Kernel265

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel266
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
  base := (-2942354619740463306191533633470289037477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-13280019246692023777989267080000000000000)
      constant := (434280932386849828376207866821529710962523) }

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
  base := (-2942354619740583565804297739768730903297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (624)
      previous := (216)
      next := (0)
      square := (3529069987324331535843979900000000000000)
      linear := (-478211139586053292065831471420000000000000)
      constant := (16095693856099000202161511623292094418384605) }

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
end ForestUnimodality.Stage170KernelData.Cell001.Kernel266

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel267
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
  base := (-2860527661824325987025011325124357195899/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-13330434532225228514215609650000000000000)
      constant := (437689066067130622231899998721125642804101) }

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
  base := (-178782978864026964525726942678193108743/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 306250000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (3087936238908790093863482412500000000000)
      linear := (-420022828632092579748732328447500000000000)
      constant := (14194039762986078805873001855226685376715930) }

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
end ForestUnimodality.Stage170KernelData.Cell001.Kernel267

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel268
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
  base := (-694513985804062983115645112606587821497/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-6690424908879216625220976110000000000000)
      constant := (220555224164743327003522312414786824357006) }

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
  base := (-1389027971608172193671882948130416492383/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2184)
      previous := (756)
      next := (0)
      square := (12351744955635160375453929650000000000000)
      linear := (-1686443640505554115759448477610000000000000)
      constant := (57219102045978167599552669479444047959366165) }

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
end ForestUnimodality.Stage170KernelData.Cell001.Kernel268

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel269
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
  base := (-2694939472828021397183588544451798977809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-13431265103291637986668294790000000000000)
      constant := (444545079165006143446962397611798201022191) }

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
  base := (-538987894565620492184472255132077047391/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-3385591932965475825047935282860000000000000)
      constant := (115327514954712729564065747235831205616946025) }

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
end ForestUnimodality.Stage170KernelData.Cell001.Kernel269

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel270
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
  base := (-2611178259490398772604232735102155850061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-13481680388824842722894637360000000000000)
      constant := (447992958564858326160237119939897844149939) }

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
  base := (-163198641218154365486676772032129570547/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 306250000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (3087936238908790093863482412500000000000)
      linear := (-424787073114980427322121701312500000000000)
      constant := (14527531336249284539272322993179256510431970) }

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
end ForestUnimodality.Stage170KernelData.Cell001.Kernel270

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel271
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
  base := (-2526772311954159064548813542979705549089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-13532095674358047459120979930000000000000)
      constant := (451454086520292427141044491293270294450911) }

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
  base := (-101070892478168855247104152976530276671/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-3411001236874211012106011938140000000000000)
      constant := (117116411295657035615299942096786752055390125) }

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
end ForestUnimodality.Stage170KernelData.Cell001.Kernel271

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel272
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
  base := (-2441721638891097724634434662603191815351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-13582510959891252195347322500000000000000)
      constant := (454928463022636650937767407977396808184649) }

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
  base := (-2441721638891152361348699960115914243201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-3423705888828578605635050265780000000000000)
      constant := (118015996769576417618867588684043601010415755) }

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
end ForestUnimodality.Stage170KernelData.Cell001.Kernel272

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel273
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
  base := (-1178013124447512081944508540084270642641/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-6816463122712228465786832535000000000000)
      constant := (229208044031648594069688974503040729357359) }

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
  base := (-2356026248895072066578406385160177178917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (624)
      previous := (216)
      next := (0)
      square := (3529069987324331535843979900000000000000)
      linear := (-490915791540420885594869799060000000000000)
      constant := (16988429587092419864529048964135393798737905) }

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
end ForestUnimodality.Stage170KernelData.Cell001.Kernel273

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel274
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
  base := (-1134843075241369634718579929972972904239/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-6841670765478830833900003820000000000000)
      constant := (230958480816878618929375757657527027095761) }

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
  base := (-283710768810347658445991290136968098221/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 306250000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (3087936238908790093863482412500000000000)
      linear := (-431139399092164224086640865132500000000000)
      constant := (14978180289222747965623176065277442815935855) }

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
end ForestUnimodality.Stage170KernelData.Cell001.Kernel274

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel275
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
  base := (-2182701352094997237698598052634427896229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-13733756816490866404026350210000000000000)
      constant := (465431083725576045899468371853615572103771) }

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
  base := (-1091350676047517029316731417186030799193/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2184)
      previous := (756)
      next := (0)
      square := (12351744955635160375453929650000000000000)
      linear := (-1730909922345840693111082624350000000000000)
      constant := (60367651189956783442803159596289422454197715) }

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
end ForestUnimodality.Stage170KernelData.Cell001.Kernel275

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel276
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
  base := (-130941991381090751893914489454800199009/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-6892086051012035570126346390000000000000)
      constant := (234479227165193979149949609224361598407928) }

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
  base := (-209507186209748431186059391989902032237/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2184)
      previous := (756)
      next := (0)
      square := (12351744955635160375453929650000000000000)
      linear := (-1737262248323024489875601788170000000000000)
      constant := (60824293652996051667452552605636370010509675) }

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
end ForestUnimodality.Stage170KernelData.Cell001.Kernel276

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel277
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
  base := (-501699422195397187967476142973626885237/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-6917293693778637938239517675000000000000)
      constant := (236249536719950744977711705862177746229526) }

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
  base := (-250849711097702131667778174359706025289/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 306250000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (3087936238908790093863482412500000000000)
      linear := (-435903643575052071660030237997500000000000)
      constant := (15320662136248272405186125704135872023804195) }

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
end ForestUnimodality.Stage170KernelData.Cell001.Kernel277

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel278
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
  base := (-191787884036564024199815265565367158083/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-6942501336545240306352688960000000000000)
      constant := (238026470522949204013221607649673164209585) }

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
  base := (-1917878840365665053810081143217644525101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-3499933800554784166809280231620000000000000)
      constant := (123485431729882327576528748106463677091350255) }

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
end ForestUnimodality.Stage170KernelData.Cell001.Kernel278

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel279
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
  base := (-914157662497744583532141475693297784533/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-6967708979311842674465860245000000000000)
      constant := (239810028570116414923290861152431702215467) }

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
  base := (-36566306499910218384977982935723499849/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2184)
      previous := (756)
      next := (0)
      square := (12351744955635160375453929650000000000000)
      linear := (-1756319226254575880169159279630000000000000)
      constant := (62204495611842403550779035912922693563424875) }

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
end ForestUnimodality.Stage170KernelData.Cell001.Kernel279

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel280
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
  base := (-173810715074555589102017754477103378101/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-6992916622078445042579031530000000000000)
      constant := (241600210857415167525943525327614483109495) }

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
  base := (-869053575372787480325143392841742094849/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 175000000000000000000000000000000000000000
      center := (312)
      previous := (108)
      next := (0)
      square := (1764534993662165767921989950000000000000)
      linear := (-251810221747394239561954063350000000000000)
      constant := (8952569683529670345741716641650539026680285) }

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
end ForestUnimodality.Stage170KernelData.Cell001.Kernel280

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel281
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
  base := (-1647254325619672397981273246023178847459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-14036248529690094821384405630000000000000)
      constant := (486794034761687091658243763540226821152541) }

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
  base := (-1647254325619689115687372749910243286587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-3538047756417886947396395214540000000000000)
      constant := (126266384765113121968276715049199990394786185) }

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
end ForestUnimodality.Stage170KernelData.Cell001.Kernel281

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel282
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
  base := (-12154350449624551041279589850067463451/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-7043331907611649778805374100000000000000)
      constant := (245200448136434497910157821757095682339136) }

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
  base := (-1555756857551957188970410123901372280581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-3550752408372254540925433542180000000000000)
      constant := (127200218808834163053106606018436163791257655) }

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
end ForestUnimodality.Stage170KernelData.Cell001.Kernel282

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel283
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
  base := (-292722950881517764732531634796621140267/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-14137079100756504293837090770000000000000)
      constant := (494021006240510825011367752712266894298665) }

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
  base := (-731807377203800835760804477370945913391/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2184)
      previous := (756)
      next := (0)
      square := (12351744955635160375453929650000000000000)
      linear := (-1781728530163311067227235934910000000000000)
      constant := (64068738849325764292286632214640118251219205) }

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
end ForestUnimodality.Stage170KernelData.Cell001.Kernel283

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel284
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
  base := (-1370828023983786131373197183337814601983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-14187494386289709030063433340000000000000)
      constant := (497654364656815404369144779216662185398017) }

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
  base := (-685414011991898697140050380527384219971/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2184)
      previous := (756)
      next := (0)
      square := (12351744955635160375453929650000000000000)
      linear := (-1788080856140494863991755098730000000000000)
      constant := (64539080716327455364548301529834790866107105) }

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
end ForestUnimodality.Stage170KernelData.Cell001.Kernel284

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel285
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
  base := (-319349168502620597843951414977245748113/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-7118954835911456883144887955000000000000)
      constant := (250650485757026392979343160948170508503774) }

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
  base := (-1277396674010492264745769437807517238807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-3588866364235357321512548525100000000000000)
      constant := (130022270008950472249339150355337158276492285) }

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
end ForestUnimodality.Stage170KernelData.Cell001.Kernel285

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel286
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
  base := (-591660356075603337575634835899207963927/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-7144162478678059251258059240000000000000)
      constant := (252480413402279720354255797341600792036073) }

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
  base := (-1183320712151215330320156720190607363793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-3601571016189724915041586852740000000000000)
      constant := (130969803425660648528687528591161301195870715) }

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
end ForestUnimodality.Stage170KernelData.Cell001.Kernel286

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel287
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
  base := (-136075018250483102416270742147304581777/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-7169370121444661619371230525000000000000)
      constant := (254316965260368731390995010429535781672892) }

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
  base := (-1088600146003872406519803437472881477707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (624)
      previous := (216)
      next := (0)
      square := (3529069987324331535843979900000000000000)
      linear := (-516325095449156072652946454340000000000000)
      constant := (18845823097274850377477169323424449148280255) }

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
end ForestUnimodality.Stage170KernelData.Cell001.Kernel287

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel288
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
  base := (-124154372887690356502154462814394237971/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-7194577764211263987484401810000000000000)
      constant := (256160141327526893075508429588742423048116) }

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
  base := (-993234983101529502935719105416049072033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-3626980320098460102099663508020000000000000)
      constant := (132875144772894783417947323042405067977351915) }

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
end ForestUnimodality.Stage170KernelData.Cell001.Kernel288

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel289
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
  base := (-897225230913178444596171764302609333191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-14439570813955732711195146190000000000000)
      constant := (516019883200039413144208416841947390666809) }

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
  base := (-897225230913184274718138827537158502713/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-3639684972052827695628701835660000000000000)
      constant := (133832952699743236429997134326101396166835315) }

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
end ForestUnimodality.Stage170KernelData.Cell001.Kernel289

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel290
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
  base := (-800570896844520611760835690362987037357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-14489986099488937447421488760000000000000)
      constant := (519732732148288654746870832284637012962643) }

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
  base := (-800570896844525722327070288228534985471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-3652389624007195289157740163300000000000000)
      constant := (134794185459654917873376917232384008928559605) }

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
end ForestUnimodality.Stage170KernelData.Cell001.Kernel290

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel291
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
  base := (-140654397647735575534114007428020025499/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-14540401385022142183647831330000000000000)
      constant := (523458829492458382434844762949109899872505) }

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
  base := (-175817997059670589360364607816879227351/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 612500000000000000000000000000000000000000
      center := (1092)
      previous := (378)
      next := (0)
      square := (6175872477817580187726964825000000000000)
      linear := (-916273568990390720671694622735000000000000)
      constant := (33939710762707690315681332562506864589299005) }

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
end ForestUnimodality.Stage170KernelData.Cell001.Kernel291

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel292
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
  base := (-605328512376955121352504280292565680737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (18)
      previous := (6)
      next := (0)
      square := (100830571066409472452685140000000000000)
      linear := (-14590816670555346919874173900000000000000)
      constant := (527198175225267291329103079359707434319263) }

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
  base := (-605328512376959048145623344878323964419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-3677798927915930476215816818580000000000000)
      constant := (136726925471486846905361714957416810628717345) }

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
end ForestUnimodality.Stage170KernelData.Cell001.Kernel292

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel293
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
  base := (-126685119119889827463389461604986295487/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-7320615978044275828050258235000000000000)
      constant := (265475384669747587231299431044915027409026) }

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
  base := (-506740476479562751891952669406489174031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-3690503579870298069744855146220000000000000)
      constant := (137698432719854224096710236382667410152362405) }

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
end ForestUnimodality.Stage170KernelData.Cell001.Kernel293

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel294
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
  base := (-20375394385315716155095090515338492957/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-7345823620810878196163429520000000000000)
      constant := (267358305913991103977701970032346615070430) }

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
  base := (-407507887706317340196345196561629211149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 350000000000000000000000000000000000000000
      center := (624)
      previous := (216)
      next := (0)
      square := (3529069987324331535843979900000000000000)
      linear := (-529029747403523666181984781980000000000000)
      constant := (19810480684882676569749928474544342977609785) }

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
end ForestUnimodality.Stage170KernelData.Cell001.Kernel294

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel295
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
  base := (-153815376578682535039032669885193054323/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-7371031263577480564276600805000000000000)
      constant := (269247851341814123449268892058239806945677) }

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
  base := (-9613461036167741083241497355659284737/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 306250000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (3087936238908790093863482412500000000000)
      linear := (-464489110472379157100366475187500000000000)
      constant := (17456465211590105884885787082816453900957740) }

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
end ForestUnimodality.Stage170KernelData.Cell001.Kernel295

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel296
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
  base := (-51777269968467772881252584584827451639/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-7396238906344082932389772090000000000000)
      constant := (271144020949696065875628716170830345096722) }

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
  base := (-25888634984234176196307246090728551169/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 306250000000000000000000000000000000000000
      center := (546)
      previous := (189)
      next := (0)
      square := (3087936238908790093863482412500000000000)
      linear := (-466077191966675106291496266142500000000000)
      constant := (17579187926719434160415365113103771504963595) }

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
end ForestUnimodality.Stage170KernelData.Cell001.Kernel296

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel297
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
  base := (-52971437419344920157942062001290775587/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-7421446549110685300502943375000000000000)
      constant := (273046814734145502530344868711123709224413) }

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
  base := (-10594287483869187212011602173872725703/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1225000000000000000000000000000000000000000
      center := (2184)
      previous := (756)
      next := (0)
      square := (12351744955635160375453929650000000000000)
      linear := (-1870661093843884221930504228390000000000000)
      constant := (70809354977785907263197247392873005911013825) }

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
end ForestUnimodality.Stage170KernelData.Cell001.Kernel297

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel298
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
  base := (-2066072488524913227524329720045848969/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-7446654191877287668616114660000000000000)
      constant := (274956232691699819158415168697779954151031) }

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
  base := (-4132144977051607346356976959568585319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2450000000000000000000000000000000000000000
      center := (4368)
      previous := (1512)
      next := (0)
      square := (24703489911270320750907859300000000000000)
      linear := (-3754026839642136037390046784420000000000000)
      constant := (142607341316473189824567772854156905696596845) }

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
end ForestUnimodality.Stage170KernelData.Cell001.Kernel298

namespace ForestUnimodality.Stage170KernelData.Cell001.Kernel299
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
  base := (49161551421393095143709471641943940021/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5000000000000000000000000000000000000000
      center := (9)
      previous := (3)
      next := (0)
      square := (50415285533204736226342570000000000000)
      linear := (-7471861834643890036729285945000000000000)
      constant := (276872274818924884379954577574766943940021) }

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
  base := (4916155142139231466934115539130627979/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 612500000000000000000000000000000000000000
      center := (1092)
      previous := (378)
      next := (0)
      square := (6175872477817580187726964825000000000000)
      linear := (-941682872899125907729771278015000000000000)
      constant := (35899849373694218700691695395157435019274275) }

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
end ForestUnimodality.Stage170KernelData.Cell001.Kernel299
