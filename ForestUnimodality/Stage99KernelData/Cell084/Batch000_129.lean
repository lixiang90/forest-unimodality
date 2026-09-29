import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell084.Parameters
import ForestUnimodality.BinomialMassData.Q53_103.Batch000_049
import ForestUnimodality.BinomialMassData.Q53_103.Batch050_099
import ForestUnimodality.BinomialMassData.Q53_103.Batch100_149
import ForestUnimodality.BinomialMassData.Q21967_42642.Batch000_049
import ForestUnimodality.BinomialMassData.Q21967_42642.Batch050_099
import ForestUnimodality.BinomialMassData.Q21967_42642.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree000.table
  base := (2495413354876231795175911549/50000000000000000000000000)
  polynomial :=
    { denominator := 200000000000000000000000000000000000000
      center := (2)
      previous := (1)
      next := (1)
      square := (19004206558161815254770488000000000000)
      linear := (-655626063127856713308450060000000000)
      constant := (9981653419504927180703646196000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree000.table
  base := (2495413354876231795175911549/50000000000000000000000000)
  polynomial :=
    { denominator := 200000000000000000000000000000000000000
      center := (2)
      previous := (1)
      next := (1)
      square := (19004206558161815254770488000000000000)
      linear := (-655626063127856713308450060000000000)
      constant := (9981653419504927180703646196000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree001.table
  base := (138907276150089642992635313176661128493887/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (5040390684388467450946502679800000000000000)
      linear := (-5361086602643353270576838366763500000000000)
      constant := (1475091339648813310230083065732936412191647183) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree001.table
  base := (17347721241439954202388727698067438913619/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215975700435361441805606693326750200000000000000)
      linear := (-229970442766681649330351298161604211500000000000)
      constant := (63149270315115152955303732907435370844749908587032) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (24988522174567113069/50000000000000000000)
  directionHi := (49977044349134226139/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree002.table
  base := (20415110649038686492924239476771728967337/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (5040390684388467450946502679800000000000000)
      linear := (-10548284782693620744366443066363500000000000)
      constant := (871852870258724102408695597959362090457912932) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree002.table
  base := (163062235957393136795159480949418223268839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431951400870722883611213386653500400000000000000)
      linear := (-904979881027344330708332841837839223000000000000)
      constant := (74599529745259386036813441411841306271812330837399) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24988522174567113069/50000000000000000000)
  centralHi := (49977044349134226139/100000000000000000000)
  directionLo := (17669553481466818341/25000000000000000000)
  directionHi := (14135642785173454673/20000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree003.table
  base := (102237810493876895959228648211069249028659/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (10080781368776934901893005359600000000000000)
      linear := (-31470965925487776436312095531927000000000000)
      constant := (1109200058231176677273941988559264662945043331) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree003.table
  base := (51016144445769991252874732945773412602339/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (23997300048373493533956299258527800000000000000)
      linear := (-75001048695629186819775727075137223500000000000)
      constant := (2635392186982033716443493694623448626143799001211) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17669553481466818341/25000000000000000000)
  centralHi := (14135642785173454673/20000000000000000000)
  directionLo := (86562780024823531863/100000000000000000000)
  directionHi := (10820347503102941483/12500000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree004.table
  base := (68195596818423779889957591231150814854707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (10080781368776934901893005359600000000000000)
      linear := (-41845362285588311383891304931127000000000000)
      constant := (766909152159882106052670491780386994793586563) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree004.table
  base := (1701114791120353382712628330164174154913/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 454585041000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (43195140087072288361121338665350040000000000000)
      linear := (-179505787201530639480359333286710082300000000000)
      constant := (3279685279289927747050845414208885763969065825732) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86562780024823531863/100000000000000000000)
  centralHi := (10820347503102941483/12500000000000000000)
  directionLo := (99954088698268452277/100000000000000000000)
  directionHi := (49977044349134226139/50000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree005.table
  base := (6013160361604070312520801471048298846833/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (5040390684388467450946502679800000000000000)
      linear := (-26109879322844423165735257165163500000000000)
      constant := (288986116078530035913533022830098109864205188) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree005.table
  base := (1499866655604377782288197175616957220571/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215975700435361441805606693326750200000000000000)
      linear := (-1120048433754643713425611789190865811500000000000)
      constant := (12361147646058950017556063620987338825786225254576) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99954088698268452277/100000000000000000000)
  centralHi := (49977044349134226139/50000000000000000000)
  directionLo := (55876034239592931283/50000000000000000000)
  directionHi := (111752068479185862567/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree006.table
  base := (35418835249946253811578481608345941818097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (10080781368776934901893005359600000000000000)
      linear := (-62594155005789381279049723729527000000000000)
      constant := (472921211169642067917591901471804096748191073) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree006.table
  base := (35337695043181100862776648285046877048689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (5050944900)
      previous := (2525472450)
      next := (2525472450)
      square := (47994600096746987067912598517055600000000000000)
      linear := (-298348429222585384322094869321818047000000000000)
      constant := (2248528433293453158540553232197795205900027562361) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55876034239592931283/50000000000000000000)
  centralHi := (111752068479185862567/100000000000000000000)
  directionLo := (24483651501564856011/20000000000000000000)
  directionHi := (15302282188478035007/12500000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree007.table
  base := (5364746285474679312746368348655990251901/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (212180)
      previous := (106090)
      next := (106090)
      square := (2016156273755386980378601071920000000000000)
      linear := (-14593710273177983245325786625745400000000000)
      constant := (83322707678823424849601427220399200582417709) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree007.table
  base := (26761383055127414891640482118805204589989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431951400870722883611213386653500400000000000000)
      linear := (-3130174858497249490946484069410993223000000000000)
      constant := (17835969628679689727852723017638772423053537754549) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24483651501564856011/20000000000000000000)
  centralHi := (15302282188478035007/12500000000000000000)
  directionLo := (2066044228278985427/1562500000000000000)
  directionHi := (132226830609855067329/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree008.table
  base := (5153271174266689427979291484548576927977/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (5040390684388467450946502679800000000000000)
      linear := (-41671473862995225587104071263963500000000000)
      constant := (195470426266316072723495253761859705257815986) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree008.table
  base := (20563226191662929074247287685081100362531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431951400870722883611213386653500400000000000000)
      linear := (-3575213853991230522994114314925624023000000000000)
      constant := (16745518666579262925531317101197863580626269498771) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2066044228278985427/1562500000000000000)
  centralHi := (132226830609855067329/100000000000000000000)
  directionLo := (17669553481466818341/12500000000000000000)
  directionHi := (141356427851734546729/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree009.table
  base := (7941540243026474372534047757519070708197/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (5040390684388467450946502679800000000000000)
      linear := (-46858672043045493060893675963563500000000000)
      constant := (193157292390256226400319508260766321143261973) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree009.table
  base := (1584181034116813755232447342820850380679/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5612161000000000000000000000000000000000000000
      center := (56121610)
      previous := (28060805)
      next := (28060805)
      square := (533273334408299856310139983522840000000000000)
      linear := (-4963275122821248833384869827704018300000000000)
      constant := (20439053879569464657923672986356444943281837319) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17669553481466818341/12500000000000000000)
  centralHi := (141356427851734546729/100000000000000000000)
  directionLo := (9370695815462667401/6250000000000000000)
  directionHi := (149931133047402678417/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree010.table
  base := (12136354526964481071715382190691296294197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (10080781368776934901893005359600000000000000)
      linear := (-104091740446191521069366561326327000000000000)
      constant := (397458197625256359842055408059813962385135973) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree010.table
  base := (6050655633952804858736773681303076460603/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215975700435361441805606693326750200000000000000)
      linear := (-2232645922489596293544687402977442811500000000000)
      constant := (8520460137882103255829906823643856748769349639723) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9370695815462667401/6250000000000000000)
  centralHi := (149931133047402678417/100000000000000000000)
  directionLo := (158041290866511505003/100000000000000000000)
  directionHi := (39510322716627876251/25000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree011.table
  base := (2271257559399050639747767691262478222529/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (5040390684388467450946502679800000000000000)
      linear := (-57233068403146028008472885362763500000000000)
      constant := (210658804203124703796821772710330762925620322) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree011.table
  base := (4527388071095879354585510609137014725389/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215975700435361441805606693326750200000000000000)
      linear := (-2455165420236586809568502525734758211500000000000)
      constant := (9035467051335651995869050744766932746308562305949) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158041290866511505003/100000000000000000000)
  centralHi := (39510322716627876251/25000000000000000000)
  directionLo := (16575510423702982347/10000000000000000000)
  directionHi := (165755104237029823471/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree012.table
  base := (3276085933684656594674586168175176171589/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (5040390684388467450946502679800000000000000)
      linear := (-62420266583196295482262490062363500000000000)
      constant := (228007852872800553334629016172632444004387701) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree012.table
  base := (40786254129065380997784844704389877811/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 50509449000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (4799460009674698706791259851705560000000000000)
      linear := (-59504109288523940568718169966490524700000000000)
      constant := (217394270729886080474184965960619631150574978224) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16575510423702982347/10000000000000000000)
  centralHi := (165755104237029823471/100000000000000000000)
  directionLo := (86562780024823531863/50000000000000000000)
  directionHi := (173125560049647063727/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree013.table
  base := (442189040141263203898036928494487030271/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10609000000000000000000000000000000000000000
      center := (106090)
      previous := (53045)
      next := (53045)
      square := (1008078136877693490189300535960000000000000)
      linear := (-13521492952649312591210418952392700000000000)
      constant := (50032302308454309864820581820678112904145039) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree013.table
  base := (4398794256190667922748288737514149194969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431951400870722883611213386653500400000000000000)
      linear := (-5800408831461135683232265542498778023000000000000)
      constant := (21472025322139238710391352603013895536375099858729) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86562780024823531863/50000000000000000000)
  centralHi := (173125560049647063727/100000000000000000000)
  directionLo := (180194795996941267681/100000000000000000000)
  directionHi := (90097397998470633841/50000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree014.table
  base := (2613616044878821738269893166725807310233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (10080781368776934901893005359600000000000000)
      linear := (-145589325886593660859683398923127000000000000)
      constant := (553384795469539981376243824581672089754261897) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree014.table
  base := (2593353764594002277233650287209625411809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431951400870722883611213386653500400000000000000)
      linear := (-6245447826955116715279895788013408823000000000000)
      constant := (23754006896317037607350357388589386790421836149169) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180194795996941267681/100000000000000000000)
  centralHi := (90097397998470633841/50000000000000000000)
  directionLo := (186996977158066942889/100000000000000000000)
  directionHi := (18699697715806694289/10000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree015.table
  base := (534233215733591835730855278990904073713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (5040390684388467450946502679800000000000000)
      linear := (-77981861123347097903631304161163500000000000)
      constant := (307288169938253821619408146438892001318021217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree015.table
  base := (525345846963970633694880170202306245341/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (23997300048373493533956299258527800000000000000)
      linear := (-371693712358283208184862557418224423500000000000)
      constant := (1465816954099595050411940805130057090731432727109) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186996977158066942889/100000000000000000000)
  centralHi := (18699697715806694289/10000000000000000000)
  directionLo := (12097516278554146889/6250000000000000000)
  directionHi := (7742410418274654009/4000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree016.table
  base := (-129128972472597744912173638623400491059/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (5040390684388467450946502679800000000000000)
      linear := (-83169059303397365377420908860763500000000000)
      constant := (341711719622494048367569006487660344190355069) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree016.table
  base := (-136917194390468746621802644111064296043/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215975700435361441805606693326750200000000000000)
      linear := (-3567762908971539389687578139521335211500000000000)
      constant := (14671913186171347821562872529057685512429656707237) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12097516278554146889/6250000000000000000)
  centralHi := (7742410418274654009/4000000000000000000)
  directionLo := (39981635479307380911/20000000000000000000)
  directionHi := (49977044349134226139/25000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree017.table
  base := (-1401416637769878957781605560494464182561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (10080781368776934901893005359600000000000000)
      linear := (-176712514966895265702421027120727000000000000)
      constant := (759556268572838067747049997599023229487210351) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree017.table
  base := (-707523171040838391648919487085515075001/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215975700435361441805606693326750200000000000000)
      linear := (-3790282406718529905711393262278650611500000000000)
      constant := (16307770497985389501223941829504232773374552339959) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39981635479307380911/20000000000000000000)
  centralHi := (49977044349134226139/25000000000000000000)
  directionLo := (51515158176914660091/25000000000000000000)
  directionHi := (41212126541531728073/20000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree018.table
  base := (-2388695489185637306324476380732104693097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (10080781368776934901893005359600000000000000)
      linear := (-187086911326995800650000236519927000000000000)
      constant := (842681108760382979255894248896999101310933927) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree018.table
  base := (-2400602089505744285361844981064548049943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (561216100)
      previous := (280608050)
      next := (280608050)
      square := (5332733344082998563101399835228400000000000000)
      linear := (-99081528505321491894696503334221383000000000000)
      constant := (446756495881165850421006151409832373951483843177) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51515158176914660091/25000000000000000000)
  centralHi := (41212126541531728073/20000000000000000000)
  directionLo := (212034641777601820093/100000000000000000000)
  directionHi := (106017320888800910047/50000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree019.table
  base := (-405293618854835013507445080239270371561/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (5040390684388467450946502679800000000000000)
      linear := (-98730653843548167798789722959563500000000000)
      constant := (466280931165054096952943668939597822512437404) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree019.table
  base := (-650546631150762266774954926795464117143/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 909170082000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (86390280174144576722242677330700080000000000000)
      linear := (-1694128560885004375103609403117312564600000000000)
      constant := (8009785152997222619358608511312996495594520542137) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (212034641777601820093/100000000000000000000)
  centralHi := (106017320888800910047/50000000000000000000)
  directionLo := (10892244290736328369/5000000000000000000)
  directionHi := (217844885814726567381/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree020.table
  base := (-1990203631223560488195086096884073878027/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (5040390684388467450946502679800000000000000)
      linear := (-103917852023598435272579327659163500000000000)
      constant := (514503623234422122186216753956926860228011557) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree020.table
  base := (-3989449592954414092841771915170460080689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431951400870722883611213386653500400000000000000)
      linear := (-8915681799919002907565677261101193623000000000000)
      constant := (44192302691520553891138255434727075092231127626751) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10892244290736328369/5000000000000000000)
  centralHi := (217844885814726567381/100000000000000000000)
  directionLo := (223504136958371725133/100000000000000000000)
  directionHi := (111752068479185862567/50000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree021.table
  base := (-230877745524115877313806774576703147331/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10609000000000000000000000000000000000000000
      center := (106090)
      previous := (53045)
      next := (53045)
      square := (1008078136877693490189300535960000000000000)
      linear := (-21821010040729740549273786471752700000000000)
      constant := (113186147345961649750624398135533212619930842) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree021.table
  base := (-4625417460571130712745117994919132584477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (5050944900)
      previous := (2525472450)
      next := (2525472450)
      square := (47994600096746987067912598517055600000000000000)
      linear := (-1040080088379220437734811945179536047000000000000)
      constant := (5401193330526133017288160549235515088100120776827) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223504136958371725133/100000000000000000000)
  centralHi := (111752068479185862567/50000000000000000000)
  directionLo := (229023588740072613047/100000000000000000000)
  directionHi := (28627948592509076631/12500000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree022.table
  base := (-1033158855393117754259652649872668877287/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (212180)
      previous := (106090)
      next := (106090)
      square := (2016156273755386980378601071920000000000000)
      linear := (-45716899353479588088063414823345400000000000)
      constant := (248199442006312156105755983223839655880862217) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree022.table
  base := (-1034524419828570514186152737596280817853/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 909170082000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (86390280174144576722242677330700080000000000000)
      linear := (-1961151958181392994332187550426091044600000000000)
      constant := (10659757851621954398258651111886377149168780463027) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229023588740072613047/100000000000000000000)
  centralHi := (28627948592509076631/12500000000000000000)
  directionLo := (46882623288914729531/20000000000000000000)
  directionHi := (29301639555571705957/12500000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree023.table
  base := (-2817480276367800056254697645779181446981/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (5040390684388467450946502679800000000000000)
      linear := (-119479446563749237693948141757963500000000000)
      constant := (678155057322534845781865867254714164028978571) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree023.table
  base := (-1128176585790026612481095990983129562577/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1718658000000000000000000000000000000000000000
      center := (17186580)
      previous := (8593290)
      next := (8593290)
      square := (163308658174186345410666686825520000000000000)
      linear := (-3875538293535329301969212853552017400000000000)
      constant := (22023435455604327713295215543017310956120269167) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46882623288914729531/20000000000000000000)
  centralHi := (29301639555571705957/12500000000000000000)
  directionLo := (119840742365787868937/50000000000000000000)
  directionHi := (1917451877852605903/800000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree024.table
  base := (-301656427620288940647362490113740902183/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10609000000000000000000000000000000000000000
      center := (106090)
      previous := (53045)
      next := (53045)
      square := (1008078136877693490189300535960000000000000)
      linear := (-24933328948759901033547549291512700000000000)
      constant := (147771452159190938098971228431031445537481106) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree024.table
  base := (-150956506083977033024935462066348935251/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50509449000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (4799460009674698706791259851705560000000000000)
      linear := (-118842642021054744841735536035107964700000000000)
      constant := (705185205020399075978882986412312178154941253204) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119840742365787868937/50000000000000000000)
  centralHi := (1917451877852605903/800000000000000000)
  directionLo := (24483651501564856011/10000000000000000000)
  directionHi := (244836515015648560111/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree025.table
  base := (-1273387601018132871902258830130864905373/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (212180)
      previous := (106090)
      next := (106090)
      square := (2016156273755386980378601071920000000000000)
      linear := (-51941537169539909056610940462865400000000000)
      constant := (321027997997180739878041023240526654218897843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree025.table
  base := (-3185690247563780608409184941463789488047/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215975700435361441805606693326750200000000000000)
      linear := (-5570438388694454033901914244337173811500000000000)
      constant := (34469910993549281995063469773548273911810785495073) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24483651501564856011/10000000000000000000)
  centralHi := (244836515015648560111/100000000000000000000)
  directionLo := (124942610872835565347/50000000000000000000)
  directionHi := (49977044349134226139/20000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree026.table
  base := (-6641855721060283819103489979490335878663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (10080781368776934901893005359600000000000000)
      linear := (-270082082207800080230633911713527000000000000)
      constant := (1738528522436897929612447319117989026663264233) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree026.table
  base := (-3322849223014836088081230618579524470709/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215975700435361441805606693326750200000000000000)
      linear := (-5792957886441444549925729367094489211500000000000)
      constant := (37334483866378332018654132591939234393222245935931) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124942610872835565347/50000000000000000000)
  centralHi := (49977044349134226139/20000000000000000000)
  directionLo := (127416962183963718739/50000000000000000000)
  directionHi := (254833924367927437479/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree027.table
  base := (-3431193998980925750775504553633360914471/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (5040390684388467450946502679800000000000000)
      linear := (-140228239283950307589106560556363500000000000)
      constant := (938916155816576387521741213617043174058377161) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree027.table
  base := (-274628381418873410318087002919745718633/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2244864400000000000000000000000000000000000000
      center := (22448644)
      previous := (11224322)
      next := (11224322)
      square := (213309333763319942524055993409136000000000000)
      linear := (-5941212231297219818221772335656103320000000000)
      constant := (39828178829285598047856743482371579087970904087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127416962183963718739/50000000000000000000)
  centralHi := (254833924367927437479/100000000000000000000)
  directionLo := (259688340074470595589/100000000000000000000)
  directionHi := (25968834007447059559/10000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree028.table
  base := (-1758063333055129263736072255096964594643/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (5040390684388467450946502679800000000000000)
      linear := (-145415437464000575062896165255963500000000000)
      constant := (1011505954023046911533359494628830605230864826) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree028.table
  base := (-7035122535197549689150457129191623090763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431951400870722883611213386653500400000000000000)
      linear := (-12475993763870851163946719225218240023000000000000)
      constant := (86887419224583501781359441656733375414428954923717) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259688340074470595589/100000000000000000000)
  centralHi := (25968834007447059559/10000000000000000000)
  directionLo := (2066044228278985427/781250000000000000)
  directionHi := (264453661219710134657/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree029.table
  base := (-1788630804058180540453723125489026201589/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (5040390684388467450946502679800000000000000)
      linear := (-150602635644050842536685769955563500000000000)
      constant := (1087017363106443611936089827811390342054684598) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree029.table
  base := (-7157000275531243084100413513097255396991/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431951400870722883611213386653500400000000000000)
      linear := (-12921032759364832195994349470732870823000000000000)
      constant := (93373646701748555270289180420796808472871374988369) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2066044228278985427/781250000000000000)
  centralHi := (264453661219710134657/100000000000000000000)
  directionLo := (269134620393557969457/100000000000000000000)
  directionHi := (134567310196778984729/50000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree030.table
  base := (-7231737142693947310356035693011918212413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (10080781368776934901893005359600000000000000)
      linear := (-311579667648202220020950749310327000000000000)
      constant := (2330873824655526624960622596289146559684510483) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree030.table
  base := (-7233874569867097977634442826010740007677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (5050944900)
      previous := (2525472450)
      next := (2525472450)
      square := (47994600096746987067912598517055600000000000000)
      linear := (-1485119083873201469782442190694166847000000000000)
      constant := (11123288181811433077437872444188039189129978960027) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269134620393557969457/100000000000000000000)
  centralHi := (134567310196778984729/50000000000000000000)
  directionLo := (273735545474569083329/100000000000000000000)
  directionHi := (27373554547456908333/10000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree031.table
  base := (-1453199337734391820363629737309590238139/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (212180)
      previous := (106090)
      next := (106090)
      square := (2016156273755386980378601071920000000000000)
      linear := (-64390812801660550993705991741905400000000000)
      constant := (498701381548580018091876399680039957163583349) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree031.table
  base := (-908480026842078374159090705469771321209/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215975700435361441805606693326750200000000000000)
      linear := (-6905555375176397130044804980881066211500000000000)
      constant := (53547153882539682368779758768015349856500330261724) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273735545474569083329/100000000000000000000)
  centralHi := (27373554547456908333/10000000000000000000)
  directionLo := (278260406486685072263/100000000000000000000)
  directionHi := (34782550810835634033/12500000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree032.table
  base := (-7259042588078871572393015939010938128133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (10080781368776934901893005359600000000000000)
      linear := (-332328460368403289916109168108727000000000000)
      constant := (2661915508028934002558499220657496957398637003) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree032.table
  base := (-3630315988911330451368281160581961995821/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215975700435361441805606693326750200000000000000)
      linear := (-7128074872923387646068620103638381611500000000000)
      constant := (57163500244319865645393094036720347790269268886339) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (278260406486685072263/100000000000000000000)
  centralHi := (34782550810835634033/12500000000000000000)
  directionLo := (282712855703469093457/100000000000000000000)
  directionHi := (141356427851734546729/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree033.table
  base := (-7212317944094423297398324986819918301083/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (10080781368776934901893005359600000000000000)
      linear := (-342702856728503824863688377507927000000000000)
      constant := (2836084315631994514712428915987168486743810453) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree033.table
  base := (-1803421932043418412620939918650934853917/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (23997300048373493533956299258527800000000000000)
      linear := (-816732707852264240232492802932855223500000000000)
      constant := (6767056565179091344310671098640560858637513676534) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282712855703469093457/100000000000000000000)
  centralHi := (141356427851734546729/50000000000000000000)
  directionLo := (17943516384525683757/6250000000000000000)
  directionHi := (287096262152410940113/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree034.table
  base := (-7127020131600402020130690591648090780169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (10080781368776934901893005359600000000000000)
      linear := (-353077253088604359811267586907127000000000000)
      constant := (3016000627601960740752537298382623404913187079) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree034.table
  base := (-1425640052101121578226117582478098086579/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 909170082000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (86390280174144576722242677330700080000000000000)
      linear := (-3029245547366947471246500139661204964600000000000)
      constant := (25906763718439250416594961322077182631110463735261) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17943516384525683757/6250000000000000000)
  centralHi := (287096262152410940113/100000000000000000000)
  directionLo := (145706870723175916143/50000000000000000000)
  directionHi := (291413741446351832287/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree035.table
  base := (-3502071729096941002896205556021698990569/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (5040390684388467450946502679800000000000000)
      linear := (-181725824724352447379423398153163500000000000)
      constant := (1600826947664767659899646592279013295409053479) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree035.table
  base := (-54727811588194137724764002576308565603/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215975700435361441805606693326750200000000000000)
      linear := (-7795633366164359194140065471910327811500000000000)
      constant := (68753475783070470938989020895083703623659379537728) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145706870723175916143/50000000000000000000)
  centralHi := (291413741446351832287/100000000000000000000)
  directionLo := (295668181692985904191/100000000000000000000)
  directionHi := (4619815338952904753/1562500000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree036.table
  base := (-3422257132484817940773229503428216532763/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (5040390684388467450946502679800000000000000)
      linear := (-186913022904402714853213002852763500000000000)
      constant := (1696517676081021904525562299848716050803917333) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree036.table
  base := (-13690778904825748290378591699843682257/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1122432200000000000000000000000000000000000000
      center := (11224322)
      previous := (5612161)
      next := (5612161)
      square := (106654666881659971262027996704568000000000000)
      linear := (-3959581661190789980327842268971675660000000000)
      constant := (35981739021501101079052280449267342563408726230) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295668181692985904191/100000000000000000000)
  centralHi := (4619815338952904753/1562500000000000000)
  directionLo := (299862266094805356833/100000000000000000000)
  directionHi := (149931133047402678417/50000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree037.table
  base := (-51943904965068150227959151021556296233/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (5040390684388467450946502679800000000000000)
      linear := (-192100221084452982327002607552363500000000000)
      constant := (1795068853353881283702432268793912292208902592) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree037.table
  base := (-6649573219104410743906974100388355542791/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431951400870722883611213386653500400000000000000)
      linear := (-16481344723316680452375391434849917223000000000000)
      constant := (154190781954639847518790313762106081718157776010569) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299862266094805356833/100000000000000000000)
  centralHi := (149931133047402678417/50000000000000000000)
  directionLo := (303998492741966047321/100000000000000000000)
  directionHi := (151999246370983023661/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree038.table
  base := (-6417632228575976215846150918784059679373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (10080781368776934901893005359600000000000000)
      linear := (-394574838529006499601584424503927000000000000)
      constant := (3792954889995892030399146476952345910861531843) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree038.table
  base := (-1604570151853299719491663296289609352327/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215975700435361441805606693326750200000000000000)
      linear := (-8463191859405330742211510840182274011500000000000)
      constant := (81450454733583554564281265176803820218896894519186) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303998492741966047321/100000000000000000000)
  centralHi := (151999246370983023661/50000000000000000000)
  directionLo := (61615838402560915843/20000000000000000000)
  directionHi := (19254949500800286201/6250000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree039.table
  base := (-768928493032426843239227343675855008637/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (5040390684388467450946502679800000000000000)
      linear := (-202474617444553517274581816951563500000000000)
      constant := (2000740923418180927434279894215172916853480268) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree039.table
  base := (-6151985831191419431876184432012312710887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (5050944900)
      previous := (2525472450)
      next := (2525472450)
      square := (47994600096746987067912598517055600000000000000)
      linear := (-1930158079367182501830072436208797647000000000000)
      constant := (19095134444904200864906107525930726119257401328737) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61615838402560915843/20000000000000000000)
  centralHi := (19254949500800286201/6250000000000000000)
  directionLo := (312106541926211220073/100000000000000000000)
  directionHi := (156053270963105610037/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree040.table
  base := (-5850604167770668618325163359089477343617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (10080781368776934901893005359600000000000000)
      linear := (-415323631249207569496742843302327000000000000)
      constant := (4215714363491474040276114063038499734861567247) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree040.table
  base := (-5851084093747308324587975808865611631431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431951400870722883611213386653500400000000000000)
      linear := (-17816461709798623548518282171393809623000000000000)
      constant := (181056503912039865724712972848269112193035861976329) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312106541926211220073/100000000000000000000)
  centralHi := (156053270963105610037/50000000000000000000)
  directionLo := (158041290866511505003/50000000000000000000)
  directionHi := (316082581733023010007/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree041.table
  base := (-5515492198242272600867303453048043568857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (10080781368776934901893005359600000000000000)
      linear := (-425698027609308104444322052701527000000000000)
      constant := (4435648925208731525270355758433170305777996087) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree041.table
  base := (-5515904977807233247743189008315000567497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431951400870722883611213386653500400000000000000)
      linear := (-18261500705292604580565912416908440423000000000000)
      constant := (190501641367496104201350772852968686806609352987623) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158041290866511505003/50000000000000000000)
  centralHi := (316082581733023010007/100000000000000000000)
  directionLo := (320009223987197751357/100000000000000000000)
  directionHi := (160004611993598875679/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree042.table
  base := (-5146368560694674972678721985946659445367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (10080781368776934901893005359600000000000000)
      linear := (-436072423969408639391901262100727000000000000)
      constant := (4661282598334192374057904708948325889944101497) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree042.table
  base := (-20104388762144693965453601167306533127/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (23997300048373493533956299258527800000000000000)
      linear := (-1039252205599254756256307925690170623500000000000)
      constant := (11121749852308667622223580530252811919799837821056) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (320009223987197751357/100000000000000000000)
  centralHi := (160004611993598875679/50000000000000000000)
  directionLo := (161944132649784374627/50000000000000000000)
  directionHi := (64777653059913749851/20000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree043.table
  base := (-4743464208918594564061548060359657747269/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (10080781368776934901893005359600000000000000)
      linear := (-446446820329509174339480471499927000000000000)
      constant := (4892612932679090850568085626934755390959223179) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree043.table
  base := (-74121396860589815478514941795018476219/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215975700435361441805606693326750200000000000000)
      linear := (-9575789348140283322330586453968851011500000000000)
      constant := (105062983714967308996228703028125340497301307520672) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161944132649784374627/50000000000000000000)
  centralHi := (64777653059913749851/20000000000000000000)
  directionLo := (163860697972881190263/50000000000000000000)
  directionHi := (327721395945762380527/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree044.table
  base := (-4306972153871398750101637522806283867257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (10080781368776934901893005359600000000000000)
      linear := (-456821216689609709287059680899127000000000000)
      constant := (5129637880590180244318612667716736134452270487) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree044.table
  base := (-53840431334238856473694671025418459491/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 454585041000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (43195140087072288361121338665350040000000000000)
      linear := (-1959661769177454767670880315345233282300000000000)
      constant := (22030496439729624549818973861209646526601015406952) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163860697972881190263/50000000000000000000)
  centralHi := (327721395945762380527/100000000000000000000)
  directionLo := (331510208474059646941/100000000000000000000)
  directionHi := (165755104237029823471/50000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree045.table
  base := (-1918526896153495503678064751351298461343/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (5040390684388467450946502679800000000000000)
      linear := (-233597806524855122117319445149163500000000000)
      constant := (2686177864904649196663345571135146574623612113) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree045.table
  base := (-767455856837808741389583180407176665093/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 11224322000000000000000000000000000000000000000
      center := (112243220)
      previous := (56121610)
      next := (56121610)
      square := (1066546668816599712620279967045680000000000000)
      linear := (-49485572067329700515447983701152996600000000000)
      constant := (569699790891067870310350250637170863500055004027) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331510208474059646941/100000000000000000000)
  centralHi := (165755104237029823471/50000000000000000000)
  directionLo := (335256205437557587699/100000000000000000000)
  directionHi := (3352562054375575877/1000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree046.table
  base := (-13022828755590762567018314219293987977/39062500000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (5040390684388467450946502679800000000000000)
      linear := (-238785004704905389591109049848763500000000000)
      constant := (2810382523863364143837636711275252290438656896) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree046.table
  base := (-1667018970518493199588868083311538187907/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4296645000000000000000000000000000000000000000
      center := (42966450)
      previous := (21483225)
      next := (21483225)
      square := (408271645435465863526666717063800000000000000)
      linear := (-19363606505446606560306298340719843500000000000)
      constant := (228162815842166859540347937584168142700524065597) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (335256205437557587699/100000000000000000000)
  centralHi := (3352562054375575877/1000000000000000000)
  directionLo := (2711686450856914507/800000000000000000)
  directionHi := (10592525198659822293/3125000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree047.table
  base := (-559491261068573857376284503360551434939/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (212180)
      previous := (106090)
      next := (106090)
      square := (2016156273755386980378601071920000000000000)
      linear := (-97588881153982262825959461819345400000000000)
      constant := (1174972927011525283380997031771571709826732149) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree047.table
  base := (-2797622807239714027606450348859123822611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431951400870722883611213386653500400000000000000)
      linear := (-20931734678256490772851693889996225223000000000000)
      constant := (252308444884168388054560622891548670937374301837949) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2711686450856914507/800000000000000000)
  centralHi := (10592525198659822293/3125000000000000000)
  directionLo := (42828169250823632933/12500000000000000000)
  directionHi := (68525070801317812693/20000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree048.table
  base := (-22279849062333367896345601456772332369/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2121800000000000000000000000000000000000000
      center := (21218)
      previous := (10609)
      next := (10609)
      square := (201615627375538698037860107192000000000000)
      linear := (-9966376042600236981547530369918540000000000)
      constant := (122693069746372475122975271839180124651794558) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree048.table
  base := (-1114063974493612389861730918934191619563/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (23997300048373493533956299258527800000000000000)
      linear := (-1187598537430581766938851340861714223500000000000)
      constant := (14636940539959289023247753897991105142035455249213) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42828169250823632933/12500000000000000000)
  centralHi := (68525070801317812693/20000000000000000000)
  directionLo := (86562780024823531863/25000000000000000000)
  directionHi := (346251120099294127453/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree049.table
  base := (-1625509306439959226507617046915247807347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (10080781368776934901893005359600000000000000)
      linear := (-508693198490112384024955727895127000000000000)
      constant := (6400130762766863661601528831578849136011855677) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree049.table
  base := (-1625632177454283641678994321666463371219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431951400870722883611213386653500400000000000000)
      linear := (-21821812669244452836946954381025486823000000000000)
      constant := (274865677839927868685990495913547813124569412665021) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86562780024823531863/25000000000000000000)
  centralHi := (346251120099294127453/100000000000000000000)
  directionLo := (87459827610984895743/25000000000000000000)
  directionHi := (349839310443939582973/100000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree050.table
  base := (-495048012694587329425498345654359377291/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (5040390684388467450946502679800000000000000)
      linear := (-259533797425106459486267468647163500000000000)
      constant := (3335647877848875525935207223647877901366319781) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree050.table
  base := (-247550388550829435381976914863915273583/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215975700435361441805606693326750200000000000000)
      linear := (-11133425832369216934497292313270058811500000000000)
      constant := (143255329607776161198543534710663851144375491456194) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87459827610984895743/25000000000000000000)
  centralHi := (349839310443939582973/100000000000000000000)
  directionLo := (176695534814668183411/50000000000000000000)
  directionHi := (353391069629336366823/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree051.table
  base := (-64360171469512123506736689874931978577/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (212180)
      previous := (106090)
      next := (106090)
      square := (2016156273755386980378601071920000000000000)
      linear := (-105888398242062690784022829338705400000000000)
      constant := (1389629574837982361186086276784582246639276607) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree051.table
  base := (-321891478933211714949142747943762627553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (5050944900)
      previous := (2525472450)
      next := (2525472450)
      square := (47994600096746987067912598517055600000000000000)
      linear := (-2523543406692490544560246096894972047000000000000)
      constant := (33155538740251797187998323252979230476195505751703) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176695534814668183411/50000000000000000000)
  centralHi := (353391069629336366823/100000000000000000000)
  directionLo := (356907485289453958161/100000000000000000000)
  directionHi := (178453742644726979081/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree052.table
  base := (379329378999832193041738538449608280049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (10080781368776934901893005359600000000000000)
      linear := (-539816387570413988867693356092727000000000000)
      constant := (7230686621543916220858572626314415894243039841) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree052.table
  base := (379251569603918591711357375705558145807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431951400870722883611213386653500400000000000000)
      linear := (-23156929655726395933089845117569379223000000000000)
      constant := (310533225051523989359836095264271215899639559073087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (356907485289453958161/100000000000000000000)
  centralHi := (178453742644726979081/50000000000000000000)
  directionLo := (180194795996941267681/50000000000000000000)
  directionHi := (360389591993882535363/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree053.table
  base := (222651076077223374278097127064382276237/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (212180)
      previous := (106090)
      next := (106090)
      square := (2016156273755386980378601071920000000000000)
      linear := (-110038156786102904763054513098385400000000000)
      constant := (1503782316158281178703397220973402231568598333) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree053.table
  base := (222637716186852550921851774626037612189/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 909170082000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (86390280174144576722242677330700080000000000000)
      linear := (-4720393730244075393027495072616802004600000000000)
      constant := (64582154129949585971938224701634519708904478664749) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (180194795996941267681/50000000000000000000)
  centralHi := (360389591993882535363/100000000000000000000)
  directionLo := (363838374803143122377/100000000000000000000)
  directionHi := (181919187401571561189/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree054.table
  base := (939972069779068947037942310530121490193/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (5040390684388467450946502679800000000000000)
      linear := (-280282590145307529381425887445563500000000000)
      constant := (3906411200879216048478766076693893058889457537) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree054.table
  base := (1879886799938966898975772462667831009097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (561216100)
      previous := (280608050)
      next := (280608050)
      square := (5332733344082998563101399835228400000000000000)
      linear := (-296876637613757506138087723562946183000000000000)
      constant := (4142376179838900605469323642807313664143844828617) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363838374803143122377/100000000000000000000)
  centralHi := (181919187401571561189/50000000000000000000)
  directionLo := (73450954504694568033/20000000000000000000)
  directionHi := (183627386261736420083/50000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree055.table
  base := (2679367926304951573063745616934554836033/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (10080781368776934901893005359600000000000000)
      linear := (-570939576650715593710430984290327000000000000)
      constant := (8112418790255186929593856051453293692255474097) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree055.table
  base := (267931871348376406094073190978383969013/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 454585041000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (43195140087072288361121338665350040000000000000)
      linear := (-2449204664220833902923273585411327162300000000000)
      constant := (34839831229607377812353250490552789239417517334533) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (73450954504694568033/20000000000000000000)
  centralHi := (183627386261736420083/50000000000000000000)
  directionLo := (370639680691562099081/100000000000000000000)
  directionHi := (185319840345781049541/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree056.table
  base := (438937929433593531336143053024320411897/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (5040390684388467450946502679800000000000000)
      linear := (-290656986505408064329005096844763500000000000)
      constant := (4208850249518625594383895309119496060999261092) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree056.table
  base := (877865300817027477754323030969352858529/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215975700435361441805606693326750200000000000000)
      linear := (-12468542818851160030640183049813951211500000000000)
      constant := (180754142663941408153450449019053820371875745329378) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370639680691562099081/100000000000000000000)
  centralHi := (185319840345781049541/50000000000000000000)
  directionLo := (186996977158066942889/50000000000000000000)
  directionHi := (373993954316133885779/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree057.table
  base := (4376331074168039976625290182343374304699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (10080781368776934901893005359600000000000000)
      linear := (-591688369370916663605589403088727000000000000)
      constant := (8728667320243745168814318929505869857998551691) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree057.table
  base := (437629483722568470449011432214101545087/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50509449000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (4799460009674698706791259851705560000000000000)
      linear := (-282023607035514456592533292723805924700000000000)
      constant := (4165137564765015543524998473902446670722393027063) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (186996977158066942889/50000000000000000000)
  centralHi := (373993954316133885779/100000000000000000000)
  directionLo := (377318410400147012567/100000000000000000000)
  directionHi := (47164801300018376571/12500000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree058.table
  base := (1318458591290011636464479650419566777359/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (5040390684388467450946502679800000000000000)
      linear := (-301031382865508599276584306243963500000000000)
      constant := (4522659539533800107269222327702235367882003262) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree058.table
  base := (1318450819123008076672159082311860401919/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215975700435361441805606693326750200000000000000)
      linear := (-12913581814345141062687813295328582011500000000000)
      constant := (194230295685788078634578739858450701125685250187358) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (377318410400147012567/100000000000000000000)
  centralHi := (47164801300018376571/12500000000000000000)
  directionLo := (380613830264704252169/100000000000000000000)
  directionHi := (38061383026470425217/10000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree059.table
  base := (775499930894599226637741987510415773423/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (5040390684388467450946502679800000000000000)
      linear := (-306218581045558866750373910943563500000000000)
      constant := (4683827814227206104116419118000163503760978428) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree059.table
  base := (6203972778831083398568239519180054782043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431951400870722883611213386653500400000000000000)
      linear := (-26272202624184263157423256836171794823000000000000)
      constant := (402302910709042144359547009196214110658977263218763) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (380613830264704252169/100000000000000000000)
  centralHi := (38061383026470425217/10000000000000000000)
  directionLo := (383880961693393213561/100000000000000000000)
  directionHi := (191940480846696606781/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree060.table
  base := (7166814656129837049261075737937427804067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (10080781368776934901893005359600000000000000)
      linear := (-622811558451218268448327031286327000000000000)
      constant := (9695676844660503379766517381696398171573346803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree060.table
  base := (447924486413908484583758417593116531901/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (23997300048373493533956299258527800000000000000)
      linear := (-1484291201093235788303938171204801423500000000000)
      constant := (23132740754750540059678959891532556312752883460392) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383880961693393213561/100000000000000000000)
  centralHi := (191940480846696606781/50000000000000000000)
  directionLo := (12097516278554146889/3125000000000000000)
  directionHi := (387120520913732700449/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree061.table
  base := (1020283771788566706028306491097241772419/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (5040390684388467450946502679800000000000000)
      linear := (-316592977405659401697953120342763500000000000)
      constant := (5014691311764572490865636459470251051854372684) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree061.table
  base := (4081125279086590059459450664312621610219/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215975700435361441805606693326750200000000000000)
      linear := (-13581140307586112610759258663600528211500000000000)
      constant := (215359927789002950483949728031590607276748890133979) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12097516278554146889/3125000000000000000)
  centralHi := (387120520913732700449/100000000000000000000)
  directionLo := (390333194430598083097/100000000000000000000)
  directionHi := (195166597215299041549/50000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree062.table
  base := (2297589433948084540335981211111090533381/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (5040390684388467450946502679800000000000000)
      linear := (-321780175585709669171742725042363500000000000)
      constant := (5184386438683699063731166540208742118937278058) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree062.table
  base := (9190340915323046168631197624826519470091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431951400870722883611213386653500400000000000000)
      linear := (-27607319610666206253566147572715687223000000000000)
      constant := (445294472963406478133071958750983887922198615508731) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (390333194430598083097/100000000000000000000)
  centralHi := (195166597215299041549/50000000000000000000)
  directionLo := (78703928144984076311/20000000000000000000)
  directionHi := (98379910181230095389/25000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree063.table
  base := (5125535189768769456959952048327146688931/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (5040390684388467450946502679800000000000000)
      linear := (-326967373765759936645532329741963500000000000)
      constant := (5356923766162775039901436782849028199222868979) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree063.table
  base := (640690997384401714419880342530828386677/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (280608050)
      previous := (140304025)
      next := (140304025)
      square := (2666366672041499281550699917614200000000000000)
      linear := (-173162707445433254849467764310063691500000000000)
      constant := (2840204830906966672225211628996398496705212631976) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78703928144984076311/20000000000000000000)
  centralHi := (98379910181230095389/25000000000000000000)
  directionLo := (6198132684836956281/1562500000000000000)
  directionHi := (79336098365913040397/20000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree064.table
  base := (2836100560502023600558160419934870802973/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (5040390684388467450946502679800000000000000)
      linear := (-332154571945810204119321934441563500000000000)
      constant := (5532303263098673487219955175095042088697481114) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree064.table
  base := (2268877975820640410262472103451175813477/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 909170082000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (86390280174144576722242677330700080000000000000)
      linear := (-5699479520330833663532281612748989764600000000000)
      constant := (95035196373709189969511842478316542093067650397557) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6198132684836956281/1562500000000000000)
  centralHi := (79336098365913040397/20000000000000000000)
  directionLo := (399816354793073809111/100000000000000000000)
  directionHi := (49977044349134226139/12500000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree065.table
  base := (3117587095763053386472537403520394161523/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (5040390684388467450946502679800000000000000)
      linear := (-337341770125860471593111539141163500000000000)
      constant := (5710524903286359229900782416708898223319195014) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree065.table
  base := (2494067557230148774656602072784979844767/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 909170082000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (86390280174144576722242677330700080000000000000)
      linear := (-5788487319429629869941807661851915924600000000000)
      constant := (98096573704882916441880334106470733233417580330447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (399816354793073809111/100000000000000000000)
  centralHi := (49977044349134226139/12500000000000000000)
  directionLo := (402927813040867660997/100000000000000000000)
  directionHi := (201463906520433830499/50000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree066.table
  base := (13628904639625129145508058567016739949031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (10080781368776934901893005359600000000000000)
      linear := (-685057936611821478133802287681527000000000000)
      constant := (11783177329285922600669568241130962594119269879) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree066.table
  base := (13628895557605091507818748771528836456373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (5050944900)
      previous := (2525472450)
      next := (2525472450)
      square := (47994600096746987067912598517055600000000000000)
      linear := (-3265275065849125597972963172752690047000000000000)
      constant := (56225982300097423007652495868775331994022512768477) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (402927813040867660997/100000000000000000000)
  centralHi := (201463906520433830499/50000000000000000000)
  directionLo := (203007713821280528221/50000000000000000000)
  directionHi := (406015427642561056443/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree067.table
  base := (14820067502860510102650967967399072960753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (10080781368776934901893005359600000000000000)
      linear := (-695432332971922013081381497080727000000000000)
      constant := (12150989057111396490420619408670295765040628577) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree067.table
  base := (14820059720138197555742877713515422004677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431951400870722883611213386653500400000000000000)
      linear := (-29832514588136111413804298800288841223000000000000)
      constant := (521828896819009651592566906612810793619628396236757) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (203007713821280528221/50000000000000000000)
  centralHi := (406015427642561056443/100000000000000000000)
  directionLo := (204539869246589100109/50000000000000000000)
  directionHi := (409079738493178200219/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree068.table
  base := (4010958503682047303225007908674566106389/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (5040390684388467450946502679800000000000000)
      linear := (-352903364666011274014480353239963500000000000)
      constant := (6262242479333699042591519398453274943645361802) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree068.table
  base := (4010956836563496032819603605302142125163/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215975700435361441805606693326750200000000000000)
      linear := (-15138776791815046222925964522901736011500000000000)
      constant := (268934017774008595593719939442548585247710098973366) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (204539869246589100109/50000000000000000000)
  centralHi := (409079738493178200219/100000000000000000000)
  directionLo := (412121265415317280729/100000000000000000000)
  directionHi := (41212126541531728073/10000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree069.table
  base := (8650100840564594903008147501818985241661/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (5040390684388467450946502679800000000000000)
      linear := (-358090562846061541488269957939563500000000000)
      constant := (6451832503747015670731130668428354114428781549) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree069.table
  base := (17300195968084357672640602963910869787891/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 954810000000000000000000000000000000000000000
      center := (9548100)
      previous := (4774050)
      next := (4774050)
      square := (90727032318992414117037048236400000000000000)
      linear := (-6452970506012197747931014343902143000000000000)
      constant := (116393878547793217256693051948730528258217620571) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (412121265415317280729/100000000000000000000)
  centralHi := (41212126541531728073/10000000000000000000)
  directionLo := (415140509188633289509/100000000000000000000)
  directionHi := (41514050918863328951/10000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree070.table
  base := (9294584199395486114783698248485052154467/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (5040390684388467450946502679800000000000000)
      linear := (-363277761026111808962059562639163500000000000)
      constant := (6644264590638838943042816052273872918306740403) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree070.table
  base := (9294581752443891528786875597656253368303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215975700435361441805606693326750200000000000000)
      linear := (-15583815787309027254973594768416366811500000000000)
      constant := (285339278263607312026820293557211895058836407355423) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (415140509188633289509/100000000000000000000)
  centralHi := (41514050918863328951/10000000000000000000)
  directionLo := (418137952512413120659/100000000000000000000)
  directionHi := (20906897625620656033/5000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree071.table
  base := (9955366196876707978430119433464345320563/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (5040390684388467450946502679800000000000000)
      linear := (-368464959206162076435849167338763500000000000)
      constant := (6839538730599197400192732015639056739505852867) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree071.table
  base := (19910728202054458700035917235783515147163/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431951400870722883611213386653500400000000000000)
      linear := (-31612670570112035541994819782347364423000000000000)
      constant := (587449937033911172678022038067579201395797213388683) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (418137952512413120659/100000000000000000000)
  centralHi := (20906897625620656033/5000000000000000000)
  directionLo := (421114060906482175431/100000000000000000000)
  directionHi := (52639257613310271929/12500000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree072.table
  base := (21264892169593418948378047057775644892089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (10080781368776934901893005359600000000000000)
      linear := (-747304314772424687819277544076727000000000000)
      constant := (14075309831380629394824523650481485816660172201) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree072.table
  base := (21264888579777639706186373917567909953619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (561216100)
      previous := (280608050)
      next := (280608050)
      square := (5332733344082998563101399835228400000000000000)
      linear := (-395774192167975513259783333677308583000000000000)
      constant := (7462535760659693128797738834325285315093212360659) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (421114060906482175431/100000000000000000000)
  centralHi := (52639257613310271929/12500000000000000000)
  directionLo := (212034641777601820093/50000000000000000000)
  directionHi := (424069283555203640187/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree073.table
  base := (22651646463834842861216389679088408287353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (10080781368776934901893005359600000000000000)
      linear := (-757678711132525222766856753475927000000000000)
      constant := (14477226278430772317722937849536869923520527977) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree073.table
  base := (11325821694923948118585770961803905792993/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215975700435361441805606693326750200000000000000)
      linear := (-16251374280549998803045040136688313011500000000000)
      constant := (310862467349184600738771565952944504657117860417713) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (212034641777601820093/50000000000000000000)
  centralHi := (424069283555203640187/100000000000000000000)
  directionLo := (427004054098903184897/100000000000000000000)
  directionHi := (213502027049451592449/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree074.table
  base := (12035497105620292165569235859465670477183/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (5040390684388467450946502679800000000000000)
      linear := (-384026553746312878857217981437563500000000000)
      constant := (7442413395523861569744759235081320298092434447) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree074.table
  base := (24070991579275758452964358339531332078603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431951400870722883611213386653500400000000000000)
      linear := (-32947787556593978638137710518891256823000000000000)
      constant := (639228550810040085493003931208162573590736359977723) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (427004054098903184897/100000000000000000000)
  centralHi := (213502027049451592449/50000000000000000000)
  directionLo := (8598375827533345663/2000000000000000000)
  directionHi := (429918791376667283151/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree075.table
  base := (25522934512892889353123903029973169372621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (10080781368776934901893005359600000000000000)
      linear := (-778427503852726292662015172274327000000000000)
      constant := (15298111359694863407885004193285760353874136189) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree075.table
  base := (25522932259656338699962091768479585409491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (5050944900)
      previous := (2525472450)
      next := (2525472450)
      square := (47994600096746987067912598517055600000000000000)
      linear := (-3710314061343106630020593418267320847000000000000)
      constant := (72997360504954691466709539115268413264281829780459) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8598375827533345663/2000000000000000000)
  centralHi := (429918791376667283151/100000000000000000000)
  directionLo := (86562780024823531863/20000000000000000000)
  directionHi := (108203475031029414829/25000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree076.table
  base := (13503733305071685045337558727880275989063/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (5040390684388467450946502679800000000000000)
      linear := (-394400950106413413804797190836763500000000000)
      constant := (7858539988161846188175996169776207847967969367) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree076.table
  base := (675186617034095764717055931023312452433/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 454585041000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (43195140087072288361121338665350040000000000000)
      linear := (-3383786554758194070223297100992051842300000000000)
      constant := (67496801556125693666746792790329646032380263419012) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86562780024823531863/20000000000000000000)
  centralHi := (108203475031029414829/25000000000000000000)
  directionLo := (435689771629453134761/100000000000000000000)
  directionHi := (217844885814726567381/50000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree077.table
  base := (14262294931330562296978102996181884649741/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (5040390684388467450946502679800000000000000)
      linear := (-399588148286463681278586795536363500000000000)
      constant := (8070866317070469753052336875169958114249102269) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree077.table
  base := (28524588211809834341889077130574110937767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431951400870722883611213386653500400000000000000)
      linear := (-34282904543075921734280601255435149223000000000000)
      constant := (693203863572469002245391069241981533432683360143447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435689771629453134761/100000000000000000000)
  centralHi := (217844885814726567381/50000000000000000000)
  directionLo := (87709356870153906051/20000000000000000000)
  directionHi := (27409174021923095641/6250000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree078.table
  base := (30074303729930558664344835386294154096603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (10080781368776934901893005359600000000000000)
      linear := (-809550692933027897504752800471927000000000000)
      constant := (16572069327412274858289864092162000680810861227) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree078.table
  base := (7518575579280471932069788837653720285679/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (23997300048373493533956299258527800000000000000)
      linear := (-1929330196587216820351568416719432223500000000000)
      constant := (39537988240863221377887069054712000824359537761742) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87709356870153906051/20000000000000000000)
  centralHi := (27409174021923095641/6250000000000000000)
  directionLo := (88277060899482983239/20000000000000000000)
  directionHi := (110346326124353729049/25000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree079.table
  base := (31656607755653848563187251763698162280181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (10080781368776934901893005359600000000000000)
      linear := (-819925089293128432452332009871127000000000000)
      constant := (17008090051296834820864185690170956803630440229) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree079.table
  base := (6331321309340251681219476747787519893971/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 909170082000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (86390280174144576722242677330700080000000000000)
      linear := (-7034596506812776759675172349292882164600000000000)
      constant := (146081557929125688224214337273533047666189122687811) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88277060899482983239/20000000000000000000)
  centralHi := (110346326124353729049/25000000000000000000)
  directionLo := (111051421644477106377/25000000000000000000)
  directionHi := (444205686577908425509/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree080.table
  base := (33271501554599702220946766672199214522827/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (10080781368776934901893005359600000000000000)
      linear := (-830299485653228967399911219270327000000000000)
      constant := (17449794801707700616261923816575521466872671643) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree080.table
  base := (133086002080820803644117695083223145853/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90917008200000000000000000000000000000000000000
      center := (909170082)
      previous := (454585041)
      next := (454585041)
      square := (8639028017414457672224267733070008000000000000)
      linear := (-712360430591157296608469839839580832460000000000)
      constant := (14987517346596844973235130035507479837648674924865) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111051421644477106377/25000000000000000000)
  centralHi := (444205686577908425509/100000000000000000000)
  directionLo := (223504136958371725133/50000000000000000000)
  directionHi := (447008273916743450267/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree081.table
  base := (17459492400756439125325648533774453773339/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (5040390684388467450946502679800000000000000)
      linear := (-420336941006664751173745214334763500000000000)
      constant := (8948591787597119694304345821179631680081353451) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree081.table
  base := (2182436494785699406935541848442690020727/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (280608050)
      previous := (140304025)
      next := (140304025)
      square := (2666366672041499281550699917614200000000000000)
      linear := (-222611484722542258410315569367244891500000000000)
      constant := (4744370501495241891698231442973091935605306088376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223504136958371725133/50000000000000000000)
  centralHi := (447008273916743450267/100000000000000000000)
  directionLo := (1799173596568832141/400000000000000000)
  directionHi := (449793399142208035251/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree082.table
  base := (285930134545000500066287303802872100551/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (5040390684388467450946502679800000000000000)
      linear := (-425524139186715018647534819034363500000000000)
      constant := (9175128184421433162033122250721015887343715776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree082.table
  base := (1463962258590454540059952484393290568039/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 181834016400000000000000000000000000000000000000
      center := (1818340164)
      previous := (909170082)
      next := (909170082)
      square := (17278056034828915344448535466140016000000000000)
      linear := (-1460323980821833075780750099320332128920000000000)
      constant := (31521770050383179844660726503982731899436922104599) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1799173596568832141/400000000000000000)
  centralHi := (449793399142208035251/100000000000000000000)
  directionLo := (226280692323592315693/50000000000000000000)
  directionHi := (452561384647184631387/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree083.table
  base := (3831171858343908279722267702158114252539/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10609000000000000000000000000000000000000000
      center := (106090)
      previous := (53045)
      next := (53045)
      square := (1008078136877693490189300535960000000000000)
      linear := (-86142267473353057224264884746792700000000000)
      constant := (1880901318019333123005372742816814534105186251) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree083.table
  base := (38311717935956396505853796110065144441399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431951400870722883611213386653500400000000000000)
      linear := (-36953138516039807926566382728522934023000000000000)
      constant := (807744557277875336147151052609113225220064286512359) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (226280692323592315693/50000000000000000000)
  centralHi := (452561384647184631387/100000000000000000000)
  directionLo := (56914067878092035627/12500000000000000000)
  directionHi := (455312543024736285017/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree084.table
  base := (1001424217268039340302373470837419556693/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10609000000000000000000000000000000000000000
      center := (106090)
      previous := (53045)
      next := (53045)
      square := (1008078136877693490189300535960000000000000)
      linear := (-87179707109363110719022805686712700000000000)
      constant := (1927345400716809102467153480678783536307824148) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree084.table
  base := (20028484068485457717517945723239983468419/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (23997300048373493533956299258527800000000000000)
      linear := (-2077676528418543831034111831890975823500000000000)
      constant := (45982718844960973630342488499474451208758952591131) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56914067878092035627/12500000000000000000)
  centralHi := (455312543024736285017/100000000000000000000)
  directionLo := (91609435496029045219/20000000000000000000)
  directionHi := (28627948592509076631/6250000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree085.table
  base := (41834807378235584422149290057013675191149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (10080781368776934901893005359600000000000000)
      linear := (-882171467453731642137807266266327000000000000)
      constant := (19743578848012714668823294002054403080102899741) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree085.table
  base := (10458701726174637706098957879626994500863/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215975700435361441805606693326750200000000000000)
      linear := (-18921608253513884995330821609776097811500000000000)
      constant := (423938698489850174031555324417804754791013162780766) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91609435496029045219/20000000000000000000)
  centralHi := (28627948592509076631/6250000000000000000)
  directionLo := (460765582220941269429/100000000000000000000)
  directionHi := (46076558222094126943/10000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree086.table
  base := (8729046901265009340331041234649115946081/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (212180)
      previous := (106090)
      next := (106090)
      square := (2016156273755386980378601071920000000000000)
      linear := (-178509172762766435417077295133105400000000000)
      constant := (4043877540249118186303905975869396871071973329) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree086.table
  base := (21822617050712524555977278266829712936657/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215975700435361441805606693326750200000000000000)
      linear := (-19144127751260875511354636732533413211500000000000)
      constant := (434154965263240482348115986603705491696828452747937) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460765582220941269429/100000000000000000000)
  centralHi := (46076558222094126943/10000000000000000000)
  directionLo := (463468042826340205183/100000000000000000000)
  directionHi := (3620844084580782853/781250000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree087.table
  base := (45488249957048780120199242218678792341817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (10080781368776934901893005359600000000000000)
      linear := (-902920260173932712032965685064727000000000000)
      constant := (20700880565615481830634886201047662307954336553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree087.table
  base := (5686031201359166151387572233672462412879/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 252547245000000000000000000000000000000000000000
      center := (2525472450)
      previous := (1262736225)
      next := (1262736225)
      square := (23997300048373493533956299258527800000000000000)
      linear := (-2151849694334207336375383539476747623500000000000)
      constant := (49388141099821197420689508777743862317540915174684) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463468042826340205183/100000000000000000000)
  centralHi := (3620844084580782853/781250000000000000)
  directionLo := (116538709149351328261/25000000000000000000)
  directionHi := (93230967319481062609/20000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree088.table
  base := (11840963407700821841579648438837179120043/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (5040390684388467450946502679800000000000000)
      linear := (-456647328267016623490272447231963500000000000)
      constant := (10594028720032846931596027037437035266569072374) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree088.table
  base := (23681926667432905686520620446773043745803/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215975700435361441805606693326750200000000000000)
      linear := (-19589166746754856543402266978048044011500000000000)
      constant := (454953612372986027788131262302551391070880650332923) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116538709149351328261/25000000000000000000)
  centralHi := (93230967319481062609/20000000000000000000)
  directionLo := (46882623288914729531/10000000000000000000)
  directionHi := (468826232889147295311/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree089.table
  base := (49272045443471790080372110230598698231491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (10080781368776934901893005359600000000000000)
      linear := (-923669052894133781928124103863127000000000000)
      constant := (21680918323703832127573600534613074589537888019) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree089.table
  base := (1231801129762684675699232029175695004931/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 454585041000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (43195140087072288361121338665350040000000000000)
      linear := (-3962337248900369411885216420161071882300000000000)
      constant := (93107198533636959437988078635739065238530215348684) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46882623288914729531/10000000000000000000)
  centralHi := (468826232889147295311/100000000000000000000)
  directionLo := (235741246712844200559/50000000000000000000)
  directionHi := (471482493425688401119/100000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree090.table
  base := (1280320633100431826058536595000520042319/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10609000000000000000000000000000000000000000
      center := (106090)
      previous := (53045)
      next := (53045)
      square := (1008078136877693490189300535960000000000000)
      linear := (-93404344925423431687570331326232700000000000)
      constant := (2217946321577626492931035114016335068515849084) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree090.table
  base := (51212825107807585937126786473422022665463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (561216100)
      previous := (280608050)
      next := (280608050)
      square := (5332733344082998563101399835228400000000000000)
      linear := (-494671746722193520381478943791670983000000000000)
      constant := (11759022488100710483952727135089941457144227495543) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (235741246712844200559/50000000000000000000)
  centralHi := (471482493425688401119/100000000000000000000)
  directionLo := (474123872599534515009/100000000000000000000)
  directionHi := (47412387259953451501/10000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree091.table
  base := (26593096606225101304882037902796259267407/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (5040390684388467450946502679800000000000000)
      linear := (-472208922807167425911641261330763500000000000)
      constant := (11341846057823281652994710197270969014567920863) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree091.table
  base := (5318619302767328521437080555638073914703/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 454585041000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (43195140087072288361121338665350040000000000000)
      linear := (-4051345047999165618294742469263998042300000000000)
      constant := (97413373331847307034711752753105863482226293757823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (474123872599534515009/100000000000000000000)
  centralHi := (47412387259953451501/10000000000000000000)
  directionLo := (119187654438980949809/25000000000000000000)
  directionHi := (476750617755923799237/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree092.table
  base := (1103842981162249019804397707162503966391/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2121800000000000000000000000000000000000000
      center := (21218)
      previous := (10609)
      next := (10609)
      square := (201615627375538698037860107192000000000000)
      linear := (-19095844839488707735417234641214540000000000)
      constant := (463872100455545903597220477435508684579442119) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree092.table
  base := (55192148900214075164985915746526583129131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8593290000000000000000000000000000000000000000
      center := (85932900)
      previous := (42966450)
      next := (42966450)
      square := (816543290870931727053333434127600000000000000)
      linear := (-77426256097326346342145661508798887000000000000)
      constant := (1882855804651487190707262130862418796153773013099) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119187654438980949809/25000000000000000000)
  centralHi := (476750617755923799237/100000000000000000000)
  directionLo := (479362969463151475749/100000000000000000000)
  directionHi := (1917451877852605903/400000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree093.table
  base := (28615346409114056395776243141647876282071/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (5040390684388467450946502679800000000000000)
      linear := (-482583319167267960859220470729963500000000000)
      constant := (11854600968357325485309887129380222819476491239) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree093.table
  base := (57230692683311469832394731473354382152871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (5050944900)
      previous := (2525472450)
      next := (2525472450)
      square := (47994600096746987067912598517055600000000000000)
      linear := (-4600392052331068694115853909296582447000000000000)
      constant := (113130198171500230682868295776503008982776947978079) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (479362969463151475749/100000000000000000000)
  centralHi := (1917451877852605903/400000000000000000)
  directionLo := (240980580884853470553/50000000000000000000)
  directionHi := (481961161769706941107/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree094.table
  base := (11860364891335923076171661594122209628611/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (212180)
      previous := (106090)
      next := (106090)
      square := (2016156273755386980378601071920000000000000)
      linear := (-195108206938927291333204030171825400000000000)
      constant := (4846096571415091870040639514978050121949934099) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree094.table
  base := (59301824341410794755898778976665873459979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431951400870722883611213386653500400000000000000)
      linear := (-41848567466473599279090315429183872823000000000000)
      constant := (1040556921950906503984678243235064096417105365574139) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (240980580884853470553/50000000000000000000)
  centralHi := (481961161769706941107/100000000000000000000)
  directionLo := (242272711224500557043/50000000000000000000)
  directionHi := (484545422449001114087/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree095.table
  base := (15351385985743506904262763706014344488557/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (5040390684388467450946502679800000000000000)
      linear := (-492957715527368495806799680129163500000000000)
      constant := (12378723891768110406067754655093369861358202426) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree095.table
  base := (959461622570328544566763087881143627803/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215975700435361441805606693326750200000000000000)
      linear := (-21146803230983790155568972837349251811500000000000)
      constant := (531593067934603722620996263816283986807244895837536) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242272711224500557043/50000000000000000000)
  centralHi := (484545422449001114087/100000000000000000000)
  directionLo := (121778993308102065419/25000000000000000000)
  directionHi := (487115973232408261677/100000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree096.table
  base := (31770925625684976971075313559235096024223/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (5040390684388467450946502679800000000000000)
      linear := (-498144913707418763280589284828763500000000000)
      constant := (12645048357911922445471049293332821133720981807) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree096.table
  base := (254167404669013166447935720734912330731/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10101889800000000000000000000000000000000000000
      center := (101018898)
      previous := (50509449)
      next := (50509449)
      square := (959892001934939741358251970341112000000000000)
      linear := (-94974767683247914095967946489362520940000000000)
      constant := (2413465389526423938800794692966245566682642886095) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121778993308102065419/25000000000000000000)
  centralHi := (487115973232408261677/100000000000000000000)
  directionLo := (489673030031297120221/100000000000000000000)
  directionHi := (244836515015648560111/50000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree097.table
  base := (65710746360140023619022681202960176867517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (10080781368776934901893005359600000000000000)
      linear := (-1006664223774938061508757779056727000000000000)
      constant := (25828429653707825910472707152534673516387487853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree097.table
  base := (65710746288293300762483857362885129196307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431951400870722883611213386653500400000000000000)
      linear := (-43183684452955542375233206165727765223000000000000)
      constant := (1109176790194240053929051353492259246402493514643587) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (489673030031297120221/100000000000000000000)
  centralHi := (244836515015648560111/50000000000000000000)
  directionLo := (492216803148680551689/100000000000000000000)
  directionHi := (49221680314868055169/10000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree098.table
  base := (1358244585018957670444610184575614453487/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2121800000000000000000000000000000000000000
      center := (21218)
      previous := (10609)
      next := (10609)
      square := (201615627375538698037860107192000000000000)
      linear := (-20340772402700771929126739769118540000000000)
      constant := (527448931939872670008391539484529613737043583) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree098.table
  base := (67912229189586873613707288309575698185751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431951400870722883611213386653500400000000000000)
      linear := (-43628723448449523407280836411242396023000000000000)
      constant := (1132538230583057220879678995886748004381373243950791) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (492216803148680551689/100000000000000000000)
  centralHi := (49221680314868055169/10000000000000000000)
  directionLo := (494747497481070913551/100000000000000000000)
  directionHi := (30921718592566932097/6250000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree099.table
  base := (70146299908321891288319433184071154558549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (10080781368776934901893005359600000000000000)
      linear := (-1027413016495139131403916197855127000000000000)
      constant := (26922147545517129006948817372713233878711646341) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree099.table
  base := (70146299855920940552966299397083374120177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 56121610000000000000000000000000000000000000000
      center := (561216100)
      previous := (280608050)
      next := (280608050)
      square := (5332733344082998563101399835228400000000000000)
      linear := (-544120523999302523942326748848852183000000000000)
      constant := (14273379585758353573316307964644704055485666672497) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494747497481070913551/100000000000000000000)
  centralHi := (30921718592566932097/6250000000000000000)
  directionLo := (124316328177772367603/25000000000000000000)
  directionHi := (497265312711089470413/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree100.table
  base := (72412958319210479736956513853702901339367/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (10080781368776934901893005359600000000000000)
      linear := (-1037787412855239666351495407254327000000000000)
      constant := (27477532499139848353844276195861634080309344503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree100.table
  base := (905161978430814659600461115550646803501/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 454585041000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (43195140087072288361121338665350040000000000000)
      linear := (-4451880143943748547137609690227165762300000000000)
      constant := (117999333777851583405672887227155035722968168228328) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124316328177772367603/25000000000000000000)
  centralHi := (497265312711089470413/100000000000000000000)
  directionLo := (499770443491342261389/100000000000000000000)
  directionHi := (49977044349134226139/10000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree101.table
  base := (74712204472606504046741549408413054417817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (10080781368776934901893005359600000000000000)
      linear := (-1048161809215340201299074616653527000000000000)
      constant := (28038601457745016741695718702465031094318620553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree101.table
  base := (37356102217200849180186274375810856792859/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215975700435361441805606693326750200000000000000)
      linear := (-22481920217465733251711863573893144211500000000000)
      constant := (602043502287203580996734632306812127898676937022219) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (499770443491342261389/100000000000000000000)
  centralHi := (49977044349134226139/10000000000000000000)
  directionLo := (251131539810020805063/50000000000000000000)
  directionHi := (502263079620041610127/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree102.table
  base := (19261009589807464555477420352565579200473/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (5040390684388467450946502679800000000000000)
      linear := (-529268102787720368123326913026363500000000000)
      constant := (14302677210617090762997037754677663459475636114) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree102.table
  base := (77044038326612319018161028999461678083881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (5050944900)
      previous := (2525472450)
      next := (2525472450)
      square := (47994600096746987067912598517055600000000000000)
      linear := (-5045431047825049726163484154811213247000000000000)
      constant := (136491638536661736299491202244743508475632205091569) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (251131539810020805063/50000000000000000000)
  centralHi := (502263079620041610127/100000000000000000000)
  directionLo := (15773231444025678089/3125000000000000000)
  directionHi := (504743406208821698849/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree103.table
  base := (496302874820370713801612387685896466551/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1000000000000000000000000000000000000000
      center := (10)
      previous := (5)
      next := (5)
      square := (95021032790809076273852440000000000000)
      linear := (-10075507606141401368594900890300000000000)
      constant := (275028668013237508703104041428874343464816) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree103.table
  base := (79408459943414290159223163015818374706281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 428490000000000000000000000000000000000000000
      center := (4284900)
      previous := (2142450)
      next := (2142450)
      square := (40715562340533781092583032015600000000000000)
      linear := (-4322171592602453442126400946254647000000000000)
      constant := (118107886185471653068310028706904705037789434569) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15773231444025678089/3125000000000000000)
  centralHi := (504743406208821698849/100000000000000000000)
  directionLo := (126802900960792029797/25000000000000000000)
  directionHi := (507211603843168119189/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree104.table
  base := (40902734651052971938255957127540887473989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (5040390684388467450946502679800000000000000)
      linear := (-539642499147820903070906122425563500000000000)
      constant := (14877956181272836060063470938404485275211549301) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree104.table
  base := (8180546927833711877978963004586298479683/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 454585041000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (43195140087072288361121338665350040000000000000)
      linear := (-4629895742141340959956661788433018082300000000000)
      constant := (127783245770660519478490139783032956471624934222003) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126802900960792029797/25000000000000000000)
  centralHi := (507211603843168119189/100000000000000000000)
  directionLo := (127416962183963718739/25000000000000000000)
  directionHi := (509667848735854874957/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree105.table
  base := (84235066346221671664697112618316697992217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (10080781368776934901893005359600000000000000)
      linear := (-1089659394655742341089391454250327000000000000)
      constant := (30339717340239236457800991830964806848999430153) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree105.table
  base := (84235066325934007475618495714408843219371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (5050944900)
      previous := (2525472450)
      next := (2525472450)
      square := (47994600096746987067912598517055600000000000000)
      linear := (-5193777379656376736846027569982756847000000000000)
      constant := (144766936258032097358188412969684520404237815336579) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (127416962183963718739/25000000000000000000)
  centralHi := (509667848735854874957/100000000000000000000)
  directionLo := (512112312873757776577/100000000000000000000)
  directionHi := (256056156436878888289/50000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree106.table
  base := (21674312774734377060579921291379524502331/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (5040390684388467450946502679800000000000000)
      linear := (-550016895507921438018485331824763500000000000)
      constant := (15464603161277763501763623958958771750890459158) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree106.table
  base := (43348625540811282106925889051669252001451/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215975700435361441805606693326750200000000000000)
      linear := (-23594517706200685831830939187679721211500000000000)
      constant := (664108235193318362423974616092310347346018934894491) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (512112312873757776577/100000000000000000000)
  centralHi := (256056156436878888289/50000000000000000000)
  directionLo := (8039768189974849689/1562500000000000000)
  directionHi := (514545164158390380097/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree107.table
  base := (44596011778163431015567876620726463304237/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (5040390684388467450946502679800000000000000)
      linear := (-555204093687971705492274936524363500000000000)
      constant := (15762189654726443273626060414506906549194650333) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree107.table
  base := (44596011770775117032930711405409964134547/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215975700435361441805606693326750200000000000000)
      linear := (-23817037203947676347854754310437036611500000000000)
      constant := (676887294948948713408738404009351275004661577511427) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8039768189974849689/1562500000000000000)
  centralHi := (514545164158390380097/100000000000000000000)
  directionLo := (103393313308097489079/20000000000000000000)
  directionHi := (129241641635121861349/25000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree108.table
  base := (91719383715090040160373142901469164737741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (10080781368776934901893005359600000000000000)
      linear := (-1120782583736043945932129082447927000000000000)
      constant := (32125236300896308647309588570874802368702694269) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree108.table
  base := (22929845925620153851485312806714645939779/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (280608050)
      previous := (140304025)
      next := (140304025)
      square := (2666366672041499281550699917614200000000000000)
      linear := (-296784650638205763751587276953016691500000000000)
      constant := (8515906079349381249176323051679188655144072104838) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103393313308097489079/20000000000000000000)
  centralHi := (129241641635121861349/25000000000000000000)
  directionLo := (259688340074470595589/50000000000000000000)
  directionHi := (519376680148941191179/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree109.table
  base := (47139665786228327000285696405986923957813/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (5040390684388467450946502679800000000000000)
      linear := (-565578490048072240439854145923563500000000000)
      constant := (16365888648428201125364852554606211776268438117) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree109.table
  base := (3771173262467896775777671139841754057321/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 181834016400000000000000000000000000000000000000
      center := (1818340164)
      previous := (909170082)
      next := (909170082)
      square := (17278056034828915344448535466140016000000000000)
      linear := (-1940966095955332590392190764476133392920000000000)
      constant := (56224922210220357888866876309838920629439183135161) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259688340074470595589/50000000000000000000)
  centralHi := (519376680148941191179/100000000000000000000)
  directionLo := (521775661414377292039/100000000000000000000)
  directionHi := (13044391535359432301/2500000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree110.table
  base := (96871867126103154144583559279746882170641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (10080781368776934901893005359600000000000000)
      linear := (-1141531376456245015827287501246327000000000000)
      constant := (33344002297308516821852048518385304672948330369) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree110.table
  base := (48435933558461667531655223496371297155457/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215975700435361441805606693326750200000000000000)
      linear := (-24484595697188647895926199678708982811500000000000)
      constant := (715956700549794874941508803271066304296136603718737) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (521775661414377292039/100000000000000000000)
  centralHi := (13044391535359432301/2500000000000000000)
  directionLo := (262081831593820244621/50000000000000000000)
  directionHi := (524163663187640489243/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree111.table
  base := (99496990374083150210155835274938399390289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (10080781368776934901893005359600000000000000)
      linear := (-1151905772816345550774866710645527000000000000)
      constant := (33961911302232003105111288159613768479131576001) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree111.table
  base := (4974849518312574374280897120517335485149/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50509449000000000000000000000000000000000000000
      center := (505094490)
      previous := (252547245)
      next := (252547245)
      square := (4799460009674698706791259851705560000000000000)
      linear := (-549047004331903075821111440032584404700000000000)
      constant := (16204975804288614817041793293470400108556047345802) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262081831593820244621/50000000000000000000)
  centralHi := (524163663187640489243/100000000000000000000)
  directionLo := (526540834853443774817/100000000000000000000)
  directionHi := (263270417426721887409/50000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree112.table
  base := (102154701314768534463714671426354113724917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (10080781368776934901893005359600000000000000)
      linear := (-1162280169176446085722445920044727000000000000)
      constant := (34585504311609588505561942247618814792507644453) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree112.table
  base := (25538675327021883887965357806615824779897/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215975700435361441805606693326750200000000000000)
      linear := (-24929634692682628927973829924223613611500000000000)
      constant := (742613159556970467277635973145095034545636587441554) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (526540834853443774817/100000000000000000000)
  centralHi := (263270417426721887409/50000000000000000000)
  directionLo := (2066044228278985427/390625000000000000)
  directionHi := (528907322439420269313/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree113.table
  base := (104844999946799735420432952079862721259757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (10080781368776934901893005359600000000000000)
      linear := (-1172654565536546620670025129443927000000000000)
      constant := (35214781325426849329321479912425764609844762013) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree113.table
  base := (1310562499263759488730999589833145624257/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 454585041000000000000000000000000000000000000000
      center := (4545850410)
      previous := (2272925205)
      next := (2272925205)
      square := (43195140087072288361121338665350040000000000000)
      linear := (-5030430838085923888799529009396185802300000000000)
      constant := (151224889128288162746743737671662105877744711516296) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2066044228278985427/390625000000000000)
  centralHi := (528907322439420269313/100000000000000000000)
  directionLo := (531263268720803065861/100000000000000000000)
  directionHi := (265631634360401532931/50000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree114.table
  base := (107567886269043687047309775801254507238151/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (10080781368776934901893005359600000000000000)
      linear := (-1183028961896647155617604338843127000000000000)
      constant := (35849742343671764878845794590719087067289543959) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree114.table
  base := (107567886264182741232070762291331978808041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (5050944900)
      previous := (2525472450)
      next := (2525472450)
      square := (47994600096746987067912598517055600000000000000)
      linear := (-5638816375150357768893657815497387647000000000000)
      constant := (171057282099143726947925009853258410558673827679409) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (531263268720803065861/100000000000000000000)
  centralHi := (265631634360401532931/50000000000000000000)
  directionLo := (133402203330236345677/25000000000000000000)
  directionHi := (533608813320945382709/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree115.table
  base := (110323360280558318399469886623018035459079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (10080781368776934901893005359600000000000000)
      linear := (-1193403358256747690565183548242327000000000000)
      constant := (36490387366334340723480704691939453338185369111) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree115.table
  base := (110323360276412468002756285873967164587789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 8593290000000000000000000000000000000000000000
      center := (85932900)
      previous := (42966450)
      next := (42966450)
      square := (816543290870931727053333434127600000000000000)
      linear := (-96775777640542912952912193922478487000000000000)
      constant := (2962242461137538753464590610501469647078060133581) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (133402203330236345677/25000000000000000000)
  centralHi := (533608813320945382709/100000000000000000000)
  directionLo := (5359440928078812847/1000000000000000000)
  directionHi := (535944092807881284701/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree116.table
  base := (113111421980562553714801863365630871755253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (10080781368776934901893005359600000000000000)
      linear := (-1203777754616848225512762757641527000000000000)
      constant := (37136716393406290430465970148793309918451479077) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree116.table
  base := (56555710988513425146844536917569677126359/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215975700435361441805606693326750200000000000000)
      linear := (-25819712683670590992069090415252875211500000000000)
      constant := (797390530215464056362149325643048205405842668195719) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5359440928078812847/1000000000000000000)
  centralHi := (535944092807881284701/100000000000000000000)
  directionLo := (107653848157423187783/20000000000000000000)
  directionHi := (134567310196778984729/25000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree117.table
  base := (115932071368410969462836960071432995750123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (10080781368776934901893005359600000000000000)
      linear := (-1214152150976948760460341967040727000000000000)
      constant := (37788729424880766701566848035415841651913054907) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree117.table
  base := (14491508920674478392103078915866906608701/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (280608050)
      previous := (140304025)
      next := (140304025)
      square := (2666366672041499281550699917614200000000000000)
      linear := (-321509039276760265532011179481607291500000000000)
      constant := (10017160088638996683116819365997034837089976051444) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (107653848157423187783/20000000000000000000)
  centralHi := (134567310196778984729/25000000000000000000)
  directionLo := (540584387990823803043/100000000000000000000)
  directionHi := (135146096997705950761/25000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree118.table
  base := (118785308443572387052019196544370544158409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (10080781368776934901893005359600000000000000)
      linear := (-1224526547337049295407921176439927000000000000)
      constant := (38446426460752134263105520957907113102976561081) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree118.table
  base := (59392654220500670024635360653520365797821/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215975700435361441805606693326750200000000000000)
      linear := (-26264751679164572024116720660767506011500000000000)
      constant := (825511441863645274383980362798542527350037456995661) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (540584387990823803043/100000000000000000000)
  centralHi := (135146096997705950761/25000000000000000000)
  directionLo := (271444831181811627277/50000000000000000000)
  directionHi := (108577932472724650911/20000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree119.table
  base := (60835566602805895806235336629218001098517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (5040390684388467450946502679800000000000000)
      linear := (-617450471848574915177750192919563500000000000)
      constant := (19554903750507889021163727140097855273654166853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree119.table
  base := (121671133203419578133880058111723477640369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431951400870722883611213386653500400000000000000)
      linear := (-52974542353823125080281071567049642823000000000000)
      constant := (1679509908534054712939350670566306178463309725120129) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271444831181811627277/50000000000000000000)
  centralHi := (108577932472724650911/20000000000000000000)
  directionLo := (54518518914508690543/10000000000000000000)
  directionHi := (545185189145086905431/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree120.table
  base := (778684660338594135438988996830810047957/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 10609000000000000000000000000000000000000000
      center := (106090)
      previous := (53045)
      next := (53045)
      square := (1008078136877693490189300535960000000000000)
      linear := (-124527534005725036530307959523832700000000000)
      constant := (3977887254566794116451547902628573020780413008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree120.table
  base := (124589545652305986746508492188050326416019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (5050944900)
      previous := (2525472450)
      next := (2525472450)
      square := (47994600096746987067912598517055600000000000000)
      linear := (-5935509038813011790258744645840474847000000000000)
      constant := (189804556531072591754673284840528084511543264463531) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54518518914508690543/10000000000000000000)
  centralHi := (545185189145086905431/100000000000000000000)
  directionLo := (547471090949138166659/100000000000000000000)
  directionHi := (27373554547456908333/5000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree121.table
  base := (31885136447244018575102107042298311715073/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (5040390684388467450946502679800000000000000)
      linear := (-627824868208675450125329402318763500000000000)
      constant := (20226810797352794075779594111969844077970418914) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree121.table
  base := (127540545787382611155323236028216088691191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431951400870722883611213386653500400000000000000)
      linear := (-53864620344811087144376332058078904423000000000000)
      constant := (1737216184463960033262921052878044891355044697073831) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (547471090949138166659/100000000000000000000)
  centralHi := (27373554547456908333/5000000000000000000)
  directionLo := (68718435980059560941/12500000000000000000)
  directionHi := (549747487840476487529/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree122.table
  base := (130524133609785817759437930077798798048281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (10080781368776934901893005359600000000000000)
      linear := (-1266024132777451435198238014036727000000000000)
      constant := (41134054648126289417871330905754761448494213129) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree122.table
  base := (65262066804213706523236340376912076049651/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215975700435361441805606693326750200000000000000)
      linear := (-27154829670152534088211981151796767611500000000000)
      constant := (883217717793436950027964667008140341334925717870691) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68718435980059560941/12500000000000000000)
  centralHi := (549747487840476487529/100000000000000000000)
  directionLo := (552014497408166059113/100000000000000000000)
  directionHi := (276007248704083029557/50000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree123.table
  base := (13354030911642320056809463789838733401357/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10609000000000000000000000000000000000000000
      center := (106090)
      previous := (53045)
      next := (53045)
      square := (1008078136877693490189300535960000000000000)
      linear := (-127639852913755197014581722343592700000000000)
      constant := (4182017170592812376394873364516926222654996413) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree123.table
  base := (133540309115265253858427715904017582725449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 505094490000000000000000000000000000000000000000
      center := (5050944900)
      previous := (2525472450)
      next := (2525472450)
      square := (47994600096746987067912598517055600000000000000)
      linear := (-6083855370644338800941288061012018447000000000000)
      constant := (199544306905368367866767890586435328483274347267601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (552014497408166059113/100000000000000000000)
  centralHi := (276007248704083029557/50000000000000000000)
  directionLo := (554272234836515604153/100000000000000000000)
  directionHi := (277136117418257802077/50000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree124.table
  base := (27317814461749458832886284669388618539361/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21218000000000000000000000000000000000000000
      center := (212180)
      previous := (106090)
      next := (106090)
      square := (2016156273755386980378601071920000000000000)
      linear := (-257354585099530501018679286567025400000000000)
      constant := (8502394553621919215735539871643613454084080849) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree124.table
  base := (27317814461552057270632837138467127539557/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 909170082000000000000000000000000000000000000000
      center := (9091700820)
      previous := (4545850410)
      next := (4545850410)
      square := (86390280174144576722242677330700080000000000000)
      linear := (-11039947466258606048103844558924559364600000000000)
      constant := (365121232829644502275119829809155613670121747966837) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (554272234836515604153/100000000000000000000)
  centralHi := (277136117418257802077/50000000000000000000)
  directionLo := (278260406486685072263/50000000000000000000)
  directionHi := (556520812973370144527/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree125.table
  base := (139670423186650786938788716520835670572601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (10080781368776934901893005359600000000000000)
      linear := (-1297147321857753040040975642234327000000000000)
      constant := (43209457834669567893191349667804170629104724009) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree125.table
  base := (17458802898226191988299240387509753211169/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2272925205000000000000000000000000000000000000000
      center := (22729252050)
      previous := (11364626025)
      next := (11364626025)
      square := (215975700435361441805606693326750200000000000000)
      linear := (-27822388163393505636283426520068713811500000000000)
      constant := (927778820793274345528094869659925149486846566091716) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (278260406486685072263/50000000000000000000)
  centralHi := (556520812973370144527/100000000000000000000)
  directionLo := (558760342395929312833/100000000000000000000)
  directionHi := (279380171197964656417/50000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree126.table
  base := (35696090437513615463818164885772317024307/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 53045000000000000000000000000000000000000000
      center := (530450)
      previous := (265225)
      next := (265225)
      square := (5040390684388467450946502679800000000000000)
      linear := (-653760859108926787494277425816763500000000000)
      constant := (21956313452803599396977943317855368022621745926) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree126.table
  base := (35696090437334371715449046882296858790279/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 28060805000000000000000000000000000000000000000
      center := (280608050)
      previous := (140304025)
      next := (140304025)
      square := (2666366672041499281550699917614200000000000000)
      linear := (-346233427915314767312435082010197891500000000000)
      constant := (11640451817674441491079988150161829634150621965838) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (558760342395929312833/100000000000000000000)
  centralHi := (279380171197964656417/50000000000000000000)
  directionLo := (560990931474200828667/100000000000000000000)
  directionHi := (140247732868550207167/25000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree127.table
  base := (145930887998902538932569329259134497978983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (10080781368776934901893005359600000000000000)
      linear := (-1317896114577954109936134061032727000000000000)
      constant := (44621479980921897011149550851190936889059030647) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree127.table
  base := (145930887998291517909040322135621795678113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4545850410000000000000000000000000000000000000000
      center := (45458504100)
      previous := (22729252050)
      next := (22729252050)
      square := (431951400870722883611213386653500400000000000000)
      linear := (-56534854317774973336662113531166689223000000000000)
      constant := (1916192822778331082011390036699870578432328620907633) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (560990931474200828667/100000000000000000000)
  centralHi := (140247732868550207167/25000000000000000000)
  directionLo := (563212686432192167483/100000000000000000000)
  directionHi := (140803171608048041871/25000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree128.table
  base := (149110001933158748426027804652713081074207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 106090000000000000000000000000000000000000000
      center := (1060900)
      previous := (530450)
      next := (530450)
      square := (10080781368776934901893005359600000000000000)
      linear := (-1328270510938054644883713270431927000000000000)
      constant := (45336017060613277759051340693183289077116262063) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree128.table
  base := (1491100019326380546261274782503004233401/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 90917008200000000000000000000000000000000000000
      center := (909170082)
      previous := (454585041)
      next := (454585041)
      square := (8639028017414457672224267733070008000000000000)
      linear := (-1139597866265379087374194875533626400460000000000)
      constant := (38937530530634962199909694210332519879007534308882) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell084.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (563212686432192167483/100000000000000000000)
  centralHi := (140803171608048041871/25000000000000000000)
  directionLo := (113085142281387637383/20000000000000000000)
  directionHi := (141356427851734546729/25000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 53
  qDenominator := 103
  table := BinomialMassData.Q53_103.Degree129.table
  base := (15232170355280302131949624445546797417433/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10609000000000000000000000000000000000000000
      center := (106090)
      previous := (53045)
      next := (53045)
      square := (1008078136877693490189300535960000000000000)
      linear := (-133864490729815517983129247983112700000000000)
      constant := (4605623814468112812546890127767179273801546697) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q53_103.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 21967
  qDenominator := 42642
  table := BinomialMassData.Q21967_42642.Degree129.table
  base := (1523217035523593277606933718164375322653/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10101889800000000000000000000000000000000000000
      center := (101018898)
      previous := (50509449)
      next := (50509449)
      square := (959892001934939741358251970341112000000000000)
      linear := (-127610960686139856446127497827102112940000000000)
      constant := (4395120679385561173046505654136873409962800496394) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q21967_42642.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell084.Kernel129
