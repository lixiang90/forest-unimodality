import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell018.Parameters
import ForestUnimodality.BinomialMassData.Q33_85.Batch000_049
import ForestUnimodality.BinomialMassData.Q33_85.Batch050_099
import ForestUnimodality.BinomialMassData.Q33_85.Batch100_149
import ForestUnimodality.BinomialMassData.Q101_255.Batch000_049
import ForestUnimodality.BinomialMassData.Q101_255.Batch050_099
import ForestUnimodality.BinomialMassData.Q101_255.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree000.table
  base := (83373033859226284368548753/6250000000000000000000000)
  polynomial :=
    { denominator := 25000000000000000000000000000000000000000
      center := (52)
      previous := (33)
      next := (0)
      square := (799891950180877178699923025000000000000)
      linear := (2374889277294765788095531900000000000000)
      constant := (333492135436905137474195012000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree000.table
  base := (83373033859226284368548753/6250000000000000000000000)
  polynomial :=
    { denominator := 75000000000000000000000000000000000000000
      center := (154)
      previous := (101)
      next := (0)
      square := (2399675850542631536099769075000000000000)
      linear := (7124667831884297364286595700000000000000)
      constant := (1000476406310715412422585036000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree001.table
  base := (85940409872970457527204736527069165705497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (1013694495035196947718691984580000000000000)
      constant := (123720653699317123703770544217192944444443165) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree001.table
  base := (84987707417383130415319193775069165705497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (267036)
      previous := (175134)
      next := (0)
      square := (4161037924840923083596999576050000000000000)
      linear := (9057979272182012951686314142380000000000000)
      constant := (1101024688918833085869427514300256499999988485) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (48734859240489362663/100000000000000000000)
  directionHi := (6091857405061170333/12500000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree002.table
  base := (56173226086063019037991879631966566705113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (654702987794019269918166530960000000000000)
      constant := (80383207733510203703434340527223688888888285) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree002.table
  base := (439920033116302640236855638816941668589/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (267036)
      previous := (175134)
      next := (0)
      square := (4161037924840923083596999576050000000000000)
      linear := (5761784523876654273699671340960000000000000)
      constant := (707969663391627649667428112727238799999993125) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48734859240489362663/100000000000000000000)
  centralHi := (6091857405061170333/12500000000000000000)
  directionLo := (34460749449121905441/50000000000000000000)
  directionHi := (68921498898243810883/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree003.table
  base := (37328043343319983552499661876732394547917/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (295711480552841592117641077340000000000000)
      constant := (52967426449920362083091134982240310121740065) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree003.table
  base := (2263523011814218258626929293663533856611/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (44506)
      previous := (29189)
      next := (0)
      square := (693506320806820513932833262675000000000000)
      linear := (410931629261882599285504756590000000000000)
      constant := (77031530850303436866276040714234354147269480) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34460749449121905441/50000000000000000000)
  centralHi := (68921498898243810883/100000000000000000000)
  directionLo := (42205626152122581251/50000000000000000000)
  directionHi := (84411252304245162503/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree004.table
  base := (630875037663275043112930278344372856979/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-31640013344168042841442188140000000000000)
      constant := (17723930974416822018733108678936375566693100) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree004.table
  base := (24295614176196613516231860049156673066197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (267036)
      previous := (175134)
      next := (0)
      square := (4161037924840923083596999576050000000000000)
      linear := (-830604972734063082273614261880000000000000)
      constant := (306835988056942181027322135148114533225891985) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42205626152122581251/50000000000000000000)
  centralHi := (84411252304245162503/100000000000000000000)
  directionLo := (97469718480978725327/100000000000000000000)
  directionHi := (6091857405061170333/6250000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree005.table
  base := (3464584025785525633072377717956755603099/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-422271533929513763483409829900000000000000)
      constant := (24109158484669645979913174568887559232390275) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree005.table
  base := (1656697255891452747304758754492461552597/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (133518)
      previous := (87567)
      next := (0)
      square := (2080518962420461541798499788025000000000000)
      linear := (-2063399860519710880130128531650000000000000)
      constant := (103653382180791504418929767971997312457619925) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97469718480978725327/100000000000000000000)
  centralHi := (6091857405061170333/6250000000000000000)
  directionLo := (54487229067808993083/50000000000000000000)
  directionHi := (108974458135617986167/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree006.table
  base := (12021142437002442321972871272230345143481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-781263041170691441283935283520000000000000)
      constant := (16681717019710145211259117419980848732330045) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree006.table
  base := (5712599835348534232714071908746779649351/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (44506)
      previous := (29189)
      next := (0)
      square := (693506320806820513932833262675000000000000)
      linear := (-1237165744890796739707816644120000000000000)
      constant := (23787553355519421956984066891109289779936585) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54487229067808993083/50000000000000000000)
  centralHi := (108974458135617986167/100000000000000000000)
  directionLo := (119375537825560679281/100000000000000000000)
  directionHi := (59687768912780339641/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree007.table
  base := (4181017034726908303407433179349461449879/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-570127274205934559542230368570000000000000)
      constant := (5883652950937144933757773891380971795075155) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree007.table
  base := (7893662107069937386320561721191885712007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (267036)
      previous := (175134)
      next := (0)
      square := (4161037924840923083596999576050000000000000)
      linear := (-10719189217650139116233542666140000000000000)
      constant := (100390537946354489852232893626638473684651035) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119375537825560679281/100000000000000000000)
  centralHi := (59687768912780339641/50000000000000000000)
  directionLo := (25788063546014601777/20000000000000000000)
  directionHi := (64470158865036504443/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree008.table
  base := (5748207448146683916787054679132191612339/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-1499246055653046796884986190760000000000000)
      constant := (8502700080756907984701781956498016879829855) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree008.table
  base := (5376765012093657397179856354375689881179/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (267036)
      previous := (175134)
      next := (0)
      square := (4161037924840923083596999576050000000000000)
      linear := (-14015383965955497794220185467560000000000000)
      constant := (72556706699803986883567484138063846904732895) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25788063546014601777/20000000000000000000)
  centralHi := (64470158865036504443/50000000000000000000)
  directionLo := (27568599559297524353/20000000000000000000)
  directionHi := (68921498898243810883/50000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree009.table
  base := (476199676581392896916558909256192665837/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-929118781447112237342755822190000000000000)
      constant := (3176577699768396253596502787369793608537860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree009.table
  base := (3509908181356050629707327180720353537989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (89012)
      previous := (58378)
      next := (0)
      square := (1387012641613641027865666525350000000000000)
      linear := (-5770526238086952157402276089660000000000000)
      constant := (18160733578361549886227857468676732587182315) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27568599559297524353/20000000000000000000)
  centralHi := (68921498898243810883/50000000000000000000)
  directionLo := (146204577721468087991/100000000000000000000)
  directionHi := (18275572215183510999/12500000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree010.table
  base := (463165890886829178082806041124658406897/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-2217229070135402152486037098000000000000000)
      constant := (4985780693383688363995629457325656989830825) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree010.table
  base := (413733108732740335917547740731309601801/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (267036)
      previous := (175134)
      next := (0)
      square := (4161037924840923083596999576050000000000000)
      linear := (-20607773462566215150193471070400000000000000)
      constant := (43248358996326110844461520797653406857110025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (146204577721468087991/100000000000000000000)
  centralHi := (18275572215183510999/12500000000000000000)
  directionLo := (154113156647650022063/100000000000000000000)
  directionHi := (9632072290478126379/6250000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree011.table
  base := (1122495737377810571387659999747636475801/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-2576220577376579830286562551620000000000000)
      constant := (4191906639107256801128970324173334707532445) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree011.table
  base := (913814526242611777627403646741260671901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (267036)
      previous := (175134)
      next := (0)
      square := (4161037924840923083596999576050000000000000)
      linear := (-23903968210871573828180113871820000000000000)
      constant := (37044591924602516447537426282792095038072505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (154113156647650022063/100000000000000000000)
  centralHi := (9632072290478126379/6250000000000000000)
  directionLo := (161635242311487953563/100000000000000000000)
  directionHi := (40408810577871988391/25000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree012.table
  base := (138208894610225324747047999442659392597/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-2935212084617757508087088005240000000000000)
      constant := (3839478491577585132476406385946642822302665) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree012.table
  base := (-5243527772838429246093631193596189733/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (44506)
      previous := (29189)
      next := (0)
      square := (693506320806820513932833262675000000000000)
      linear := (-4533360493196155417694459445540000000000000)
      constant := (5789253239429356729131064955391042070029780) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161635242311487953563/100000000000000000000)
  centralHi := (40408810577871988391/25000000000000000000)
  directionLo := (42205626152122581251/25000000000000000000)
  directionHi := (33764500921698065001/20000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree013.table
  base := (-173903557138078589825607379349869030763/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-1647101795929467592943806729430000000000000)
      constant := (1921921796138360170692353182099878501094930) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree013.table
  base := (-213543542327025281040049545773223243493/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (133518)
      previous := (87567)
      next := (0)
      square := (2080518962420461541798499788025000000000000)
      linear := (-15248178853741145592076699737330000000000000)
      constant := (17799347347431258101945194689947463436747070) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42205626152122581251/25000000000000000000)
  centralHi := (33764500921698065001/20000000000000000000)
  directionLo := (87858016947052203033/50000000000000000000)
  directionHi := (175716033894104406067/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree014.table
  base := (-708584546486445924170785917407731014899/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-1826597549550056431844069456240000000000000)
      constant := (2074904750128753480849807646749828683470945) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree014.table
  base := (-1558895695294487881558081836596088827073/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (267036)
      previous := (175134)
      next := (0)
      square := (4161037924840923083596999576050000000000000)
      linear := (-33792552455787649862140042276080000000000000)
      constant := (39165516595468897689961574459859864803915635) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87858016947052203033/50000000000000000000)
  centralHi := (175716033894104406067/100000000000000000000)
  directionLo := (22793643258820662319/12500000000000000000)
  directionHi := (182349146070565298553/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree015.table
  base := (-3283040022546097471579104382241788581/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-4012186606341290541488664366100000000000000)
      constant := (4720609179709428535126452115437884687784375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree015.table
  base := (-272507245681288840773374610754726635991/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (44506)
      previous := (29189)
      next := (0)
      square := (693506320806820513932833262675000000000000)
      linear := (-6181457867348834756687780846250000000000000)
      constant := (7520763043926497226263343766688040131916060) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22793643258820662319/12500000000000000000)
  centralHi := (182349146070565298553/100000000000000000000)
  directionLo := (18874929821817794319/10000000000000000000)
  directionHi := (188749298218177943191/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree016.table
  base := (-523441257079107635044682915717003288701/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-4371178113582468219289189819720000000000000)
      constant := (5531100651542373322158315448312651239135275) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree016.table
  base := (-2734044644903329806656083027940619217577/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (267036)
      previous := (175134)
      next := (0)
      square := (4161037924840923083596999576050000000000000)
      linear := (-40384941952398367218113327878920000000000000)
      constant := (53262810134146252474083992047424247075411115) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18874929821817794319/10000000000000000000)
  centralHi := (188749298218177943191/100000000000000000000)
  directionLo := (38987887392391490131/20000000000000000000)
  directionHi := (6091857405061170333/3125000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree017.table
  base := (-3125350736163855935698421716126036385683/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (104)
      previous := (66)
      next := (0)
      square := (1599783900361754357399846050000000000000)
      linear := (-16367368930185625941486904060000000000000)
      constant := (22711294558647831726984164277369818071585) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree017.table
  base := (-3232443223083812462494959850949771294413/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 450000000000000000000000000000000000000000
      center := (924)
      previous := (606)
      next := (0)
      square := (14398055103255789216598614450000000000000)
      linear := (-151145801732538843931141767060000000000000)
      constant := (219479297256713073663981522669260291751415) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38987887392391490131/20000000000000000000)
  centralHi := (6091857405061170333/3125000000000000000)
  directionLo := (100469486149073259453/50000000000000000000)
  directionHi := (200938972298146518907/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree018.table
  base := (-3585264693779341064885851090460651975883/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-5089161128064823574890240726960000000000000)
      constant := (7805093839361432607865755959716357894849065) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree018.table
  base := (-29469943254835292260747041821784420439/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (89012)
      previous := (58378)
      next := (0)
      square := (1387012641613641027865666525350000000000000)
      linear := (-15659110483003028191362204493920000000000000)
      constant := (25171432149147220210746276834396567174616875) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100469486149073259453/50000000000000000000)
  centralHi := (200938972298146518907/100000000000000000000)
  directionLo := (25845562086841429081/12500000000000000000)
  directionHi := (206764496694731432649/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree019.table
  base := (-500459319727343191448470745169109087687/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-2724076317653000626345383090290000000000000)
      constant := (4622985069945297221770665744311549473169140) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree019.table
  base := (-32755074366852923296446784021705251231/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (267036)
      previous := (175134)
      next := (0)
      square := (4161037924840923083596999576050000000000000)
      linear := (-50273526197314443252073256283180000000000000)
      constant := (89433388756563442925794430905637400967605625) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25845562086841429081/12500000000000000000)
  centralHi := (206764496694731432649/100000000000000000000)
  directionLo := (212430326456972515181/100000000000000000000)
  directionHi := (106215163228486257591/50000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree020.table
  base := (-4385810607238859587280082527899132431641/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-5807144142547178930491291634200000000000000)
      constant := (10878635275944146962742451155185753636278755) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree020.table
  base := (-44694145549080671039461003731691579969/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (133518)
      previous := (87567)
      next := (0)
      square := (2080518962420461541798499788025000000000000)
      linear := (-26784860472809900965029949542300000000000000)
      constant := (52560577728050988957356779504267550125157750) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (212430326456972515181/100000000000000000000)
  centralHi := (106215163228486257591/50000000000000000000)
  directionLo := (54487229067808993083/25000000000000000000)
  directionHi := (217948916271235972333/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree021.table
  base := (-2367928933005945794927134988480036507153/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-3083067824894178304145908543910000000000000)
      constant := (6348520943941124544157970992195347247163915) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree021.table
  base := (-1203225433359958402635177403643280668143/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (44506)
      previous := (29189)
      next := (0)
      square := (693506320806820513932833262675000000000000)
      linear := (-9477652615654193434674423647670000000000000)
      constant := (20420781927201039872398232061539756607200190) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54487229067808993083/25000000000000000000)
  centralHi := (217948916271235972333/100000000000000000000)
  directionLo := (111665590726280291093/50000000000000000000)
  directionHi := (223331181452560582187/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree022.table
  base := (-5057247115424876052482009687144181555171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-6525127157029534286092342541440000000000000)
      constant := (14696232496745135948728724384148657652777905) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree022.table
  base := (-1282050342658997950110167591728784368723/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (133518)
      previous := (87567)
      next := (0)
      square := (2080518962420461541798499788025000000000000)
      linear := (-30081055221115259643016592343720000000000000)
      constant := (70800179145393653604332997847338318569514770) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111665590726280291093/50000000000000000000)
  centralHi := (223331181452560582187/100000000000000000000)
  directionLo := (114293375917183900473/50000000000000000000)
  directionHi := (228586751834367800947/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree023.table
  base := (-167276447498037778578591556550236924353/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-3442059332135355981946433997530000000000000)
      constant := (8436031446944490205808847838019522308958640) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree023.table
  base := (-1083626384641225671294317392864259151027/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (267036)
      previous := (175134)
      next := (0)
      square := (4161037924840923083596999576050000000000000)
      linear := (-63458305190535877964019827488860000000000000)
      constant := (162311501609337007027396384619539548704469325) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (114293375917183900473/50000000000000000000)
  centralHi := (228586751834367800947/100000000000000000000)
  directionLo := (233724174229747066251/100000000000000000000)
  directionHi := (58431043557436766563/25000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree024.table
  base := (-17578404863235046554632859518896032871/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-3621555085755944820846696724340000000000000)
      constant := (9610507919251021627186375233055237200224800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree024.table
  base := (-5685093404641231271001379685496944172353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (89012)
      previous := (58378)
      next := (0)
      square := (1387012641613641027865666525350000000000000)
      linear := (-22251499979613745547335490096760000000000000)
      constant := (61542303114468346616611918639754747012849745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233724174229747066251/100000000000000000000)
  centralHi := (58431043557436766563/25000000000000000000)
  directionLo := (119375537825560679281/50000000000000000000)
  directionHi := (238751075651121358563/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree025.table
  base := (-587606632521960295353068109320131130317/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-3801050839376533659746959451150000000000000)
      constant := (10870036000891400020571520286287052583459675) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree025.table
  base := (-5931150214876503233926064909083919733199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (267036)
      previous := (175134)
      next := (0)
      square := (4161037924840923083596999576050000000000000)
      linear := (-70050694687146595319993113091700000000000000)
      constant := (208519733971834094693886416589613623869747005) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119375537825560679281/50000000000000000000)
  centralHi := (238751075651121358563/100000000000000000000)
  directionLo := (243674296202446813319/100000000000000000000)
  directionHi := (6091857405061170333/2500000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree026.table
  base := (-3053792704276339553334427973686805089521/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-3980546592997122498647222177960000000000000)
      constant := (12213308847114609283617471270386566645642155) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree026.table
  base := (-1231618202578700452947721495210398531801/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (267036)
      previous := (175134)
      next := (0)
      square := (4161037924840923083596999576050000000000000)
      linear := (-73346889435451953997979755893120000000000000)
      constant := (233966713984569009516042358873775835469639975) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (243674296202446813319/100000000000000000000)
  centralHi := (6091857405061170333/2500000000000000000)
  directionLo := (248499998259452905143/100000000000000000000)
  directionHi := (31062499782431613143/12500000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree027.table
  base := (-632122207717442743242588849685423300539/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-4160042346617711337547484904770000000000000)
      constant := (13639188324666510921754634863563816653605725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree027.table
  base := (-1591868388460461247239981327542626868301/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (44506)
      previous := (29189)
      next := (0)
      square := (693506320806820513932833262675000000000000)
      linear := (-12773847363959552112661066449090000000000000)
      constant := (43491265129314836683567340862188425051830330) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (248499998259452905143/100000000000000000000)
  centralHi := (31062499782431613143/12500000000000000000)
  directionLo := (126616878456367743753/50000000000000000000)
  directionHi := (253233756912735487507/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree028.table
  base := (-1303670833207624489345300139726064920799/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-8679076200476600352895495263160000000000000)
      constant := (30293357895586728194454798903791180947227225) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree028.table
  base := (-6560659414578060536230240078040961372547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (267036)
      previous := (175134)
      next := (0)
      square := (4161037924840923083596999576050000000000000)
      linear := (-79939278932062671353953041495960000000000000)
      constant := (289444657038774965119000392713525297350026265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126616878456367743753/50000000000000000000)
  centralHi := (253233756912735487507/100000000000000000000)
  directionLo := (257880635460146017771/100000000000000000000)
  directionHi := (64470158865036504443/25000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree029.table
  base := (-3350095249751035260882691924986559064979/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-4519033853858889015348010358390000000000000)
      constant := (16734907340896292456125100573103422151105345) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree029.table
  base := (-6738841704118462986506168878414213287177/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (267036)
      previous := (175134)
      next := (0)
      square := (4161037924840923083596999576050000000000000)
      linear := (-83235473680368030031939684297380000000000000)
      constant := (319442396390469679958995596125705156200263115) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (257880635460146017771/100000000000000000000)
  centralHi := (64470158865036504443/25000000000000000000)
  directionLo := (52489049772507420061/20000000000000000000)
  directionHi := (131222624431268550153/50000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree030.table
  base := (-858474237107778029745401936036158242169/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-4698529607479477854248273085200000000000000)
      constant := (18403105617033970259093798706411005360263180) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree030.table
  base := (-6903067737094076462380867459720323533387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (89012)
      previous := (58378)
      next := (0)
      square := (1387012641613641027865666525350000000000000)
      linear := (-28843889476224462903308775699600000000000000)
      constant := (116975729501398898635688554967112397482767355) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52489049772507420061/20000000000000000000)
  centralHi := (131222624431268550153/50000000000000000000)
  directionLo := (266931817428551110819/100000000000000000000)
  directionHi := (13346590871427555541/5000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree031.table
  base := (-7022100208250496636435949935904308862491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-9756050722200133386297071624020000000000000)
      constant := (40301195248972180667854433707876273693700505) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree031.table
  base := (-705425795993119196499598436316547526221/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (133518)
      previous := (87567)
      next := (0)
      square := (2080518962420461541798499788025000000000000)
      linear := (-44913931588489373693956484950110000000000000)
      constant := (191943531487091049246681729881017497107479475) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (266931817428551110819/100000000000000000000)
  centralHi := (13346590871427555541/5000000000000000000)
  directionLo := (271344212506734062421/100000000000000000000)
  directionHi := (135672106253367031211/50000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree032.table
  base := (-3581967172141890864480987162836478558089/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-5057521114720655532048798538820000000000000)
      constant := (21976787365331946757115470312197288483561395) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree032.table
  base := (-7193221992422691617006604091569935273707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (267036)
      previous := (175134)
      next := (0)
      square := (4161037924840923083596999576050000000000000)
      linear := (-93124057925284106065899612701640000000000000)
      constant := (418311490695019455712759606748620991765440465) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271344212506734062421/100000000000000000000)
  centralHi := (135672106253367031211/50000000000000000000)
  directionLo := (27568599559297524353/10000000000000000000)
  directionHi := (275685995592975243531/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree033.table
  base := (-3647011978057151902405944676282659358879/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-5237016868341244370949061265630000000000000)
      constant := (23881149111614057479660550079072557226419845) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree033.table
  base := (-366033618974002086377342480638505764737/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (44506)
      previous := (29189)
      next := (0)
      square := (693506320806820513932833262675000000000000)
      linear := (-16070042112264910790647709250510000000000000)
      constant := (75698534170022524702494139444063775098651050) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27568599559297524353/10000000000000000000)
  centralHi := (275685995592975243531/100000000000000000000)
  directionLo := (69990112994300968631/25000000000000000000)
  directionHi := (11198418079088154981/4000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree034.table
  base := (-3706505613517225470602735798330968850037/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25000000000000000000000000000000000000000
      center := (52)
      previous := (33)
      next := (0)
      square := (799891950180877178699923025000000000000)
      linear := (-18742258207480391729582435960000000000000)
      constant := (89492106871639003860799887804345155749815) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree034.table
  base := (-929654559663910550372535283592099921473/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225000000000000000000000000000000000000000
      center := (462)
      previous := (303)
      next := (0)
      square := (7199027551627894608299307225000000000000)
      linear := (-172519805228191736024001554160000000000000)
      constant := (850377244259590983402631547157422014134860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69990112994300968631/25000000000000000000)
  centralHi := (11198418079088154981/4000000000000000000)
  directionLo := (11366824793334018007/4000000000000000000)
  directionHi := (277510370931006299/97656250000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree035.table
  base := (-752146311026537130436032757316643594943/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-5596008375582422048749586719250000000000000)
      constant := (27922587064498511115355102094112250026536825) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree035.table
  base := (-942933348444077211288583090031157563401/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (133518)
      previous := (87567)
      next := (0)
      square := (2080518962420461541798499788025000000000000)
      linear := (-51506321085100091049929770552950000000000000)
      constant := (265142415948483010343385138061504183551879980) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11366824793334018007/4000000000000000000)
  centralHi := (277510370931006299/97656250000000000)
  directionLo := (57663863096972925459/20000000000000000000)
  directionHi := (9009978608902019603/3125000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree036.table
  base := (-23812125825127656391032509789347434143/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-5775504129203010887649849446060000000000000)
      constant := (30058891921824664706920377758046873226138400) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree036.table
  base := (-1527969995842574312303578255485851898369/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (89012)
      previous := (58378)
      next := (0)
      square := (1387012641613641027865666525350000000000000)
      linear := (-35436278972835180259282061302440000000000000)
      constant := (190161743344814203756478668919768160102851925) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57663863096972925459/20000000000000000000)
  centralHi := (9009978608902019603/3125000000000000000)
  directionLo := (292409155442936175983/100000000000000000000)
  directionHi := (18275572215183510999/6250000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree037.table
  base := (-7708704878603531484396652824524945797593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-11909999765647199453100224345740000000000000)
      constant := (64543627950863644737261009810363453322478115) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree037.table
  base := (-3863407393902429837243150275871151651861/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (133518)
      previous := (87567)
      next := (0)
      square := (2080518962420461541798499788025000000000000)
      linear := (-54802515833405449727916413354370000000000000)
      constant := (306056832944564609267005216261884672767547695) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (292409155442936175983/100000000000000000000)
  centralHi := (18275572215183510999/6250000000000000000)
  directionLo := (296442575707406648641/100000000000000000000)
  directionHi := (148221287853703324321/50000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree038.table
  base := (-1947081887599349746603566345783717196607/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-6134495636444188565450374899680000000000000)
      constant := (34561071019389206119811109675081057301805770) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree038.table
  base := (-1560947789052871062876577807584490994437/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (267036)
      previous := (175134)
      next := (0)
      square := (4161037924840923083596999576050000000000000)
      linear := (-112901226415116258133819469510160000000000000)
      constant := (655165227057201110906870754002386473086734075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (296442575707406648641/100000000000000000000)
  centralHi := (148221287853703324321/50000000000000000000)
  directionLo := (300421848734794643447/100000000000000000000)
  directionHi := (37552731091849330431/12500000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree039.table
  base := (-982386666307690915358303193658165068661/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-6313991390064777404350637626490000000000000)
      constant := (36926413754321084437921091092484805903139420) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree039.table
  base := (-123030551062436558624998828682472716433/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (44506)
      previous := (29189)
      next := (0)
      square := (693506320806820513932833262675000000000000)
      linear := (-19366236860570269468634352051930000000000000)
      constant := (116605930876886118160227253659574384776414240) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (300421848734794643447/100000000000000000000)
  centralHi := (37552731091849330431/12500000000000000000)
  directionLo := (304349098409083750859/100000000000000000000)
  directionHi := (15217454920454187543/5000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree040.table
  base := (-1584261410600902116134269358287859789811/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-12986974287370732486501800706600000000000000)
      constant := (78735243875023496190324079852770213018615525) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree040.table
  base := (-7934757010420215318565496004237855714817/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (267036)
      previous := (175134)
      next := (0)
      square := (4161037924840923083596999576050000000000000)
      linear := (-119493615911726975489792755113000000000000000)
      constant := (745520926727736079379867458981686686428804915) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (304349098409083750859/100000000000000000000)
  centralHi := (15217454920454187543/5000000000000000000)
  directionLo := (308226313295300044127/100000000000000000000)
  directionHi := (9632072290478126379/3125000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree041.table
  base := (-3987619016992081751004688312530081628663/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-6672982897305955082151163080110000000000000)
      constant := (41884500988181675940308655096903032046581965) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree041.table
  base := (-1597480515144358135796735043757912542411/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (267036)
      previous := (175134)
      next := (0)
      square := (4161037924840923083596999576050000000000000)
      linear := (-122789810660032334167779397914420000000000000)
      constant := (792817890923043386475305092131283736929724725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (308226313295300044127/100000000000000000000)
  centralHi := (9632072290478126379/3125000000000000000)
  directionLo := (156027679205327834811/50000000000000000000)
  directionHi := (312055358410655669623/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree042.table
  base := (-8021124216725124099032611355938165498473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-13704957301853087842102851613840000000000000)
      constant := (88953757984557634019162094046181350854706515) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree042.table
  base := (-4016059831421113611079967441595841853671/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (44506)
      previous := (29189)
      next := (0)
      square := (693506320806820513932833262675000000000000)
      linear := (-21014334234722948807627673452640000000000000)
      constant := (140253919437083937397493459232510025564336215) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156027679205327834811/50000000000000000000)
  centralHi := (312055358410655669623/100000000000000000000)
  directionLo := (315837985711017792997/100000000000000000000)
  directionHi := (157918992855508896499/50000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree043.table
  base := (-8059175831210770744413643810364288574733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-14063948809094265519903377067460000000000000)
      constant := (94289208117280360857446534775905603009510815) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree043.table
  base := (-4034554459154532211001910360177018758417/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (133518)
      previous := (87567)
      next := (0)
      square := (2080518962420461541798499788025000000000000)
      linear := (-64691100078321525761876341758630000000000000)
      constant := (445817597209013071125320403323286871046786915) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315837985711017792997/100000000000000000000)
  centralHi := (157918992855508896499/50000000000000000000)
  directionLo := (159787921730010143313/50000000000000000000)
  directionHi := (319575843460020286627/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree044.table
  base := (-1617915725010883582545325009430541672757/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-14422940316335443197703902521080000000000000)
      constant := (99775083969230292979710984102992336414330675) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree044.table
  base := (-1619709430540487920561782959160565851689/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (267036)
      previous := (175134)
      next := (0)
      square := (4161037924840923083596999576050000000000000)
      linear := (-132678394904948410201739326318680000000000000)
      constant := (943150624888016254169907211123656205493922775) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (159787921730010143313/50000000000000000000)
  centralHi := (319575843460020286627/100000000000000000000)
  directionLo := (161635242311487953563/50000000000000000000)
  directionHi := (323270484622975907127/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree045.table
  base := (-1622499343373453595360162646250422799163/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-14781931823576620875504427974700000000000000)
      constant := (105411148389014242957217163979090695276047325) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree045.table
  base := (-1015073771758728116092595538786929588213/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (44506)
      previous := (29189)
      next := (0)
      square := (693506320806820513932833262675000000000000)
      linear := (-22662431608875628146620994853350000000000000)
      constant := (166011296958136097441297837913409640940386580) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161635242311487953563/50000000000000000000)
  centralHi := (323270484622975907127/100000000000000000000)
  directionLo := (163461687203426979249/50000000000000000000)
  directionHi := (326923374406853958499/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree046.table
  base := (-812807511650889594374702376827307005833/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-7570461665408899276652476714160000000000000)
      constant := (55598595918692562452344973071546706882856575) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree046.table
  base := (-1627075056830362460009220113506130703907/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (267036)
      previous := (175134)
      next := (0)
      square := (4161037924840923083596999576050000000000000)
      linear := (-139270784401559127557712611921520000000000000)
      constant := (1050384879391290736021571515112375850978447325) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163461687203426979249/50000000000000000000)
  centralHi := (326923374406853958499/100000000000000000000)
  directionLo := (41316987131270067139/12500000000000000000)
  directionHi := (330535897050160537113/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree047.table
  base := (-8136441951326662453177399399594581936611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-15499914838058976231105478881940000000000000)
      constant := (117133029170326002697889784333707829101597105) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree047.table
  base := (-4071511738846410185403368693407760214489/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (133518)
      previous := (87567)
      next := (0)
      square := (2080518962420461541798499788025000000000000)
      linear := (-71283489574932243117849627361470000000000000)
      constant := (553050172139393771847463342649661078410570555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41316987131270067139/12500000000000000000)
  centralHi := (330535897050160537113/100000000000000000000)
  directionLo := (21382999164925327/6400000000000000)
  directionHi := (41763670243994779297/12500000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree048.table
  base := (-4068855216407449666821264010707464262483/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-7929453172650076954453002167780000000000000)
      constant := (61609248398613783422280539520463714140712065) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree048.table
  base := (-814364138024133369886792123141688530079/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (44506)
      previous := (29189)
      next := (0)
      square := (693506320806820513932833262675000000000000)
      linear := (-24310528983028307485614316254060000000000000)
      constant := (193868798291008160998845851297751901110537675) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (21382999164925327/6400000000000000)
  centralHi := (41763670243994779297/12500000000000000000)
  directionLo := (42205626152122581251/12500000000000000000)
  directionHi := (337645009216980650009/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree049.table
  base := (-2032995148510231995497309257394737549377/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-8108948926270665793353264894590000000000000)
      constant := (64726725085153768963130082338878208482300470) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree049.table
  base := (-8137322955587132251077079045297709893669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (267036)
      previous := (175134)
      next := (0)
      square := (4161037924840923083596999576050000000000000)
      linear := (-149159368646475203591672540325780000000000000)
      constant := (1221720993793988914447165995167705282832834655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42205626152122581251/12500000000000000000)
  centralHi := (337645009216980650009/100000000000000000000)
  directionLo := (341144014683425538647/100000000000000000000)
  directionHi := (42643001835428192331/12500000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree050.table
  base := (-4059670412302820358417662748881682798389/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-8288444679891254632253527621400000000000000)
      constant := (67918880783296313271292160791365968356327895) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree050.table
  base := (-1015518876281480164485152792472618282163/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (133518)
      previous := (87567)
      next := (0)
      square := (2080518962420461541798499788025000000000000)
      linear := (-76227781697390281134829591563600000000000000)
      constant := (640811939761896826090472981369074396961880740) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (341144014683425538647/100000000000000000000)
  centralHi := (42643001835428192331/12500000000000000000)
  directionLo := (344607494491219054413/100000000000000000000)
  directionHi := (172303747245609527207/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree051.table
  base := (-1012483653345188527107962704112625613977/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25000000000000000000000000000000000000000
      center := (52)
      previous := (33)
      next := (0)
      square := (799891950180877178699923025000000000000)
      linear := (-29300831949867970488421419890000000000000)
      constant := (246317159391570955991067037018747487720460) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree051.table
  base := (-810419851917347451067007171811832996291/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 75000000000000000000000000000000000000000
      center := (154)
      previous := (101)
      next := (0)
      square := (2399675850542631536099769075000000000000)
      linear := (-89822236530038016694144074930000000000000)
      constant := (774463954957551506401535002337112525278175) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (344607494491219054413/100000000000000000000)
  centralHi := (172303747245609527207/50000000000000000000)
  directionLo := (1740182546205324707/500000000000000000)
  directionHi := (348036509241064941401/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree052.table
  base := (-8073634813543006131818955052795614475551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-17294872374264864620108106150040000000000000)
      constant := (149054020131678878673136510122342337082828805) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree052.table
  base := (-8077529793846487226520223357883222659449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (267036)
      previous := (175134)
      next := (0)
      square := (4161037924840923083596999576050000000000000)
      linear := (-159047952891391279625632468730040000000000000)
      constant := (1405610012540805501844162055821576689313865755) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1740182546205324707/500000000000000000)
  centralHi := (348036509241064941401/100000000000000000000)
  directionLo := (87858016947052203033/25000000000000000000)
  directionHi := (351432067788208812133/100000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree053.table
  base := (-8040698567325480946237222859515979024201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-17653863881506042297908631603660000000000000)
      constant := (155885779457112849203328891646761410310029555) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree053.table
  base := (-4022100755823086287831052056672152494557/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (133518)
      previous := (87567)
      next := (0)
      square := (2080518962420461541798499788025000000000000)
      linear := (-81172073819848319151809555765730000000000000)
      constant := (734845843183880767244045173402727656808286215) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (87858016947052203033/25000000000000000000)
  centralHi := (351432067788208812133/100000000000000000000)
  directionLo := (70959026141876131357/20000000000000000000)
  directionHi := (177397565354690328393/50000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree054.table
  base := (-800111437507753490674450871748710782073/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-9006427694373609987854578528640000000000000)
      constant := (81433259118980146953519658337499564599522575) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree054.table
  base := (-8004263622837093031070581515840816036761/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (89012)
      previous := (58378)
      next := (0)
      square := (1387012641613641027865666525350000000000000)
      linear := (-55213447462667332327201918110960000000000000)
      constant := (511721623258023925023669471586374062480641065) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70959026141876131357/20000000000000000000)
  centralHi := (177397565354690328393/50000000000000000000)
  directionLo := (358126613476682037843/100000000000000000000)
  directionHi := (89531653369170509461/25000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree055.table
  base := (-1988732463668498871732247998697128108597/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-9185923447994198826754841255450000000000000)
      constant := (84998083833196043542466433010090299766154670) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree055.table
  base := (-795776014980252603728912551755652515591/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (133518)
      previous := (87567)
      next := (0)
      square := (2080518962420461541798499788025000000000000)
      linear := (-84468268568153677829796198567150000000000000)
      constant := (801014495124320850213314216477213695173695225) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (358126613476682037843/100000000000000000000)
  centralHi := (89531653369170509461/25000000000000000000)
  directionLo := (361427389368137300867/100000000000000000000)
  directionHi := (90356847342034325217/25000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree056.table
  base := (-7902187084961038065074978747530027256657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-18730838403229575331310207964520000000000000)
      constant := (177274666938475505315388717431227110614130635) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree056.table
  base := (-7904729891303321541378622018823684111677/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (267036)
      previous := (175134)
      next := (0)
      square := (4161037924840923083596999576050000000000000)
      linear := (-172232731884612714337579039935720000000000000)
      constant := (1670283543213586456993423580257549988127640615) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (361427389368137300867/100000000000000000000)
  centralHi := (90356847342034325217/25000000000000000000)
  directionLo := (72939658428226119421/20000000000000000000)
  directionHi := (182349146070565298553/50000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree057.table
  base := (-7842923250785556586272771905794343666829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-19089829910470753009110733418140000000000000)
      constant := (184701962322106786847751383174169173401432095) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree057.table
  base := (-1569041408610384983689744786234897736803/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (89012)
      previous := (58378)
      next := (0)
      square := (1387012641613641027865666525350000000000000)
      linear := (-58509642210972691005188560912380000000000000)
      constant := (579976027984555230889364273518004591554794975) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72939658428226119421/20000000000000000000)
  centralHi := (182349146070565298553/50000000000000000000)
  directionLo := (2943520947935355879/800000000000000000)
  directionHi := (91985029622979871219/25000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree058.table
  base := (-7777171212894244160055878579072681392609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-19448821417711930686911258871760000000000000)
      constant := (192278006333506960138744945475791975387679995) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree058.table
  base := (-3889610872272957356376424805636443538047/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (133518)
      previous := (87567)
      next := (0)
      square := (2080518962420461541798499788025000000000000)
      linear := (-89412560690611715846776162769280000000000000)
      constant := (905481110252356699241310224057702051787698765) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2943520947935355879/800000000000000000)
  centralHi := (91985029622979871219/25000000000000000000)
  directionLo := (46394203790222757989/12500000000000000000)
  directionHi := (371153630321782063913/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree059.table
  base := (-3852480005726855177355396417351228502913/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-9903906462476554182355892162690000000000000)
      constant := (100001378504817637181097710204396474813290715) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree059.table
  base := (-7706800560923571546366056472244441045743/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (267036)
      previous := (175134)
      next := (0)
      square := (4161037924840923083596999576050000000000000)
      linear := (-182121316129528790371538968339980000000000000)
      constant := (1883385607387106234946920341284023044200112285) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46394203790222757989/12500000000000000000)
  centralHi := (371153630321782063913/100000000000000000000)
  directionLo := (74867911365612003081/20000000000000000000)
  directionHi := (187169778414030007703/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree060.table
  base := (-1525263062184686918521901649575073041133/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-20166804432194286042512309779000000000000000)
      constant := (207876177265347781752775277257020097277814075) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree060.table
  base := (-1525593381512538547369513765705828623597/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (89012)
      previous := (58378)
      next := (0)
      square := (1387012641613641027865666525350000000000000)
      linear := (-61805836959278049683175203713800000000000000)
      constant := (652399313361285315982044929283526164583535025) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74867911365612003081/20000000000000000000)
  centralHi := (187169778414030007703/50000000000000000000)
  directionLo := (377498596436355886381/100000000000000000000)
  directionHi := (188749298218177943191/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree061.table
  base := (-1508251958622536115729339049029962357279/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-20525795939435463720312835232620000000000000)
      constant := (215898234325430096256911717254096521968659225) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree061.table
  base := (-3771370712113176018407606328962984863637/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (133518)
      previous := (87567)
      next := (0)
      square := (2080518962420461541798499788025000000000000)
      linear := (-94356852813069753863756126971410000000000000)
      constant := (1016199475087421881663734480486897381848400815) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (377498596436355886381/100000000000000000000)
  centralHi := (188749298218177943191/50000000000000000000)
  directionLo := (47578927323548558233/12500000000000000000)
  directionHi := (76126283717677693173/20000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree062.table
  base := (-744981350445678621454434869634748484481/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-10442393723338320699056680343120000000000000)
      constant := (112034449611391577303308228906564942199624775) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree062.table
  base := (-7451142304750840048738396127765314679219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (267036)
      previous := (175134)
      next := (0)
      square := (4161037924840923083596999576050000000000000)
      linear := (-192009900374444866405498896744240000000000000)
      constant := (2108988401049228721805808207437540082596756905) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47578927323548558233/12500000000000000000)
  centralHi := (76126283717677693173/20000000000000000000)
  directionLo := (38373866539847050961/10000000000000000000)
  directionHi := (383738665398470509611/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree063.table
  base := (-3675997081422622257674073861930192633317/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-10621889476958909537956943069930000000000000)
      constant := (116194073177528319697574246301131871644856935) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree063.table
  base := (-229787049611207354144642761076126093833/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (44506)
      previous := (29189)
      next := (0)
      square := (693506320806820513932833262675000000000000)
      linear := (-32551015853791704180580923257610000000000000)
      constant := (364494347354554414951367271913862894131743120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38373866539847050961/10000000000000000000)
  centralHi := (383738665398470509611/100000000000000000000)
  directionLo := (386820953190219026657/100000000000000000000)
  directionHi := (193410476595109513329/50000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree064.table
  base := (-1811954357178222393668899033254665268703/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-10801385230579498376857205796740000000000000)
      constant := (120427976546461107678615264311398017373448330) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree064.table
  base := (-1812221352912881087570757529945905440893/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (133518)
      previous := (87567)
      next := (0)
      square := (2080518962420461541798499788025000000000000)
      linear := (-99301144935527791880736091173540000000000000)
      constant := (1133165907765709417049490668221402999482373070) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386820953190219026657/100000000000000000000)
  centralHi := (193410476595109513329/50000000000000000000)
  directionLo := (389878873923914901311/100000000000000000000)
  directionHi := (6091857405061170333/1562500000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree065.table
  base := (-7137297144556749852886147302133709277181/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-21961761968400174431514937047100000000000000)
      constant := (249472299433971676367643155743066790094473455) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree065.table
  base := (-3569127121092923491342786744789437508867/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (133518)
      previous := (87567)
      next := (0)
      square := (2080518962420461541798499788025000000000000)
      linear := (-100949242309680471219729412574250000000000000)
      constant := (1173542716576073777412973553250538365197184665) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (389878873923914901311/100000000000000000000)
  centralHi := (6091857405061170333/1562500000000000000)
  directionLo := (98228249130968633683/25000000000000000000)
  directionHi := (392912996523874534733/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree066.table
  base := (-7020445546556297286284539482648245100207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-22320753475641352109315462500720000000000000)
      constant := (258237167696925685478426027189741285830200885) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree066.table
  base := (-7021303069244428226788486435707607037933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (89012)
      previous := (58378)
      next := (0)
      square := (1387012641613641027865666525350000000000000)
      linear := (-68398226455888767039148489316640000000000000)
      constant := (809742264687828504267912145527871523490560445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98228249130968633683/25000000000000000000)
  centralHi := (392912996523874534733/100000000000000000000)
  directionLo := (98980967028565823171/25000000000000000000)
  directionHi := (79184773622852658537/20000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree067.table
  base := (-6897273451546457651553304983229223195081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-22679744982882529787115987954340000000000000)
      constant := (267150542251457774942272883776795772483107955) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree067.table
  base := (-862255197873781911169552562954938718627/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (133518)
      previous := (87567)
      next := (0)
      square := (2080518962420461541798499788025000000000000)
      linear := (-104245437057985829897716055375670000000000000)
      constant := (1256377886122431529704187516670793087857023460) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98980967028565823171/25000000000000000000)
  centralHi := (79184773622852658537/20000000000000000000)
  directionLo := (398912015170953286557/100000000000000000000)
  directionHi := (199456007585476643279/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree068.table
  base := (-3383895211107138372527916742703518574349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25000000000000000000000000000000000000000
      center := (52)
      previous := (33)
      next := (0)
      square := (799891950180877178699923025000000000000)
      linear := (-39859405692255549247260403820000000000000)
      constant := (477876140621946649798336725630482407128255) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree068.table
  base := (-6768478328008490867180583885633843800543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 450000000000000000000000000000000000000000
      center := (924)
      previous := (606)
      next := (0)
      square := (14398055103255789216598614450000000000000)
      linear := (-732827227904072728281725790840000000000000)
      constant := (8988485316864879424803090775898477028975565) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (398912015170953286557/100000000000000000000)
  centralHi := (199456007585476643279/50000000000000000000)
  directionLo := (100469486149073259453/25000000000000000000)
  directionHi := (401877944596293037813/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree069.table
  base := (-207250153532992084600998290041823611143/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-11698863998682442571358519430790000000000000)
      constant := (142711378282130571379493858890222038110373840) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree069.table
  base := (-1658155209827478552609076091145549811417/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (44506)
      previous := (29189)
      next := (0)
      square := (693506320806820513932833262675000000000000)
      linear := (-35847210602097062858567566059030000000000000)
      constant := (447329358176321935289060150241055083135014610) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100469486149073259453/25000000000000000000)
  centralHi := (401877944596293037813/100000000000000000000)
  directionLo := (202411072361501192587/50000000000000000000)
  directionHi := (16192885788920095407/4000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree070.table
  base := (-6489924399333852987996559899042420082289/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-23756719504606062820517564315200000000000000)
      constant := (294781573304030698493793096156883702981092395) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree070.table
  base := (-6490475762175008545987490264595877058477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (267036)
      previous := (175134)
      next := (0)
      square := (4161037924840923083596999576050000000000000)
      linear := (-218379458360887735829392039155600000000000000)
      constant := (2771667363274934748941812907221530618854506615) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (202411072361501192587/50000000000000000000)
  centralHi := (16192885788920095407/4000000000000000000)
  directionLo := (25484067890801416921/6250000000000000000)
  directionHi := (407745086252822670737/100000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree071.table
  base := (-6341555491017868962068830038030979502869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-24115711011847240498318089768820000000000000)
      constant := (304288849947388230761385586892943234618354295) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree071.table
  base := (-6342048957758958450454884253528173224409/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (267036)
      previous := (175134)
      next := (0)
      square := (4161037924840923083596999576050000000000000)
      linear := (-221675653109193094507378681957020000000000000)
      constant := (2860745823000636389971496493164828107216560955) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25484067890801416921/6250000000000000000)
  centralHi := (407745086252822670737/100000000000000000000)
  directionLo := (410647223135031208659/100000000000000000000)
  directionHi := (20532361156751560433/5000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree072.table
  base := (-1237380806690658885288798889028339775107/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-24474702519088418176118615222440000000000000)
      constant := (313944578047809492355107069999442245124851925) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree072.table
  base := (-3093672798074817546859587097356560314741/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (44506)
      previous := (29189)
      next := (0)
      square := (693506320806820513932833262675000000000000)
      linear := (-37495307976249742197560887459740000000000000)
      constant := (491868576833007295043185552268927311035597765) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (410647223135031208659/100000000000000000000)
  centralHi := (20532361156751560433/5000000000000000000)
  directionLo := (25845562086841429081/6250000000000000000)
  directionHi := (413528993389462865297/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree073.table
  base := (-94155862442313520454740891214296706447/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-12416847013164797926959570338030000000000000)
      constant := (161874375067562157929512237307911920293890720) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree073.table
  base := (-753296279796196891521929122997715512813/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (133518)
      previous := (87567)
      next := (0)
      square := (2080518962420461541798499788025000000000000)
      linear := (-114134021302901905931675983779930000000000000)
      constant := (1521532108975529400294122722778727839023467740) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25845562086841429081/6250000000000000000)
  centralHi := (413528993389462865297/100000000000000000000)
  directionLo := (416390819878263807003/100000000000000000000)
  directionHi := (104097704969565951751/25000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree074.table
  base := (-366173347010039153052413489490853577327/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-12596342766785386765859833064840000000000000)
      constant := (166850679800978424240542028604409732646099880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree074.table
  base := (-1464781727158944742798590396942124153649/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (133518)
      previous := (87567)
      next := (0)
      square := (2080518962420461541798499788025000000000000)
      linear := (-115782118677054585270669305180640000000000000)
      constant := (1568152020762369695343523461464011350763589510) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (416390819878263807003/100000000000000000000)
  centralHi := (104097704969565951751/25000000000000000000)
  directionLo := (52404138878778435451/12500000000000000000)
  directionHi := (419233111030227483609/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree075.table
  base := (-1421325786484098294786602259224275414393/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-12775838520405975604760095791650000000000000)
      constant := (171901200301694932532191457732966844052404230) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree075.table
  base := (-1137123831607005484754214154148380320221/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (89012)
      previous := (58378)
      next := (0)
      square := (1387012641613641027865666525350000000000000)
      linear := (-78286810700804843073108417720900000000000000)
      constant := (1076976961845733985360838776743583856559209825) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52404138878778435451/12500000000000000000)
  centralHi := (419233111030227483609/100000000000000000000)
  directionLo := (42205626152122581251/10000000000000000000)
  directionHi := (422056261521225812511/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree076.table
  base := (-550556755625858847867212059544186039279/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-12955334274026564443660358518460000000000000)
      constant := (177025933984156404202389278145057255866209225) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree076.table
  base := (-2752925060317420505454603545258045734091/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (133518)
      previous := (87567)
      next := (0)
      square := (2080518962420461541798499788025000000000000)
      linear := (-119078313425359943948655947982060000000000000)
      constant := (1663472354614949196199500621991935115228146545) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42205626152122581251/10000000000000000000)
  centralHi := (422056261521225812511/100000000000000000000)
  directionLo := (424860652913945030363/100000000000000000000)
  directionHi := (106215163228486257591/25000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree077.table
  base := (-2659784974827636431553598552244681430973/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-13134830027647153282560621245270000000000000)
      constant := (182224878560546315528548419674347435332244015) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree077.table
  base := (-106396451258579580228459489717865798947/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (133518)
      previous := (87567)
      next := (0)
      square := (2080518962420461541798499788025000000000000)
      linear := (-120726410799512623287649269382770000000000000)
      constant := (1712172738312288680107761470981627882117356625) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (424860652913945030363/100000000000000000000)
  centralHi := (106215163228486257591/25000000000000000000)
  directionLo := (427646654259862039247/100000000000000000000)
  directionHi := (26727915891241377453/6250000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree078.table
  base := (-1025462625690935500802229133257493856987/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-26628651562535484242921767944160000000000000)
      constant := (374996064012365038978434276878926606883268925) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree078.table
  base := (-1281884731852388372220708234503369968099/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (44506)
      previous := (29189)
      next := (0)
      square := (693506320806820513932833262675000000000000)
      linear := (-40791502724555100875547530261160000000000000)
      constant := (587188859326104823690891265352363782376581670) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (427646654259862039247/100000000000000000000)
  centralHi := (26727915891241377453/6250000000000000000)
  directionLo := (430414622666150006183/100000000000000000000)
  directionHi := (53801827833268750773/12500000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree079.table
  base := (-2464399786552011404145613610353993229579/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-13493821534888330960361146698890000000000000)
      constant := (192845392528941899340404938411347479783258345) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree079.table
  base := (-2464500685481852642822355800130087943553/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (133518)
      previous := (87567)
      next := (0)
      square := (2080518962420461541798499788025000000000000)
      linear := (-124022605547817981965635912184190000000000000)
      constant := (1811653859587867935766818167898449206294093235) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (430414622666150006183/100000000000000000000)
  centralHi := (53801827833268750773/12500000000000000000)
  directionLo := (108291225957494647941/25000000000000000000)
  directionHi := (86632980765995718353/20000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree080.table
  base := (-4724031479561366586516282468113468178919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-27346634577017839598522818851400000000000000)
      constant := (396533917084489516627951664367976038481462045) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree080.table
  base := (-2362105899354923058536984385914586025543/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (133518)
      previous := (87567)
      next := (0)
      square := (2080518962420461541798499788025000000000000)
      linear := (-125670702921970661304629233584900000000000000)
      constant := (1862434570752916602011031344165180808737813285) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108291225957494647941/25000000000000000000)
  centralHi := (86632980765995718353/20000000000000000000)
  directionLo := (54487229067808993083/12500000000000000000)
  directionHi := (87179566508494388933/20000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree081.table
  base := (-282063174520897688256202550612783410629/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-13852813042129508638161672152510000000000000)
      constant := (203762728641184316269638978264945223773128760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree081.table
  base := (-1128292973453846089509956970587961162433/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (44506)
      previous := (29189)
      next := (0)
      square := (693506320806820513932833262675000000000000)
      linear := (-42439600098707780214540851661870000000000000)
      constant := (637969566842888132282575399835369376721705890) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54487229067808993083/12500000000000000000)
  centralHi := (87179566508494388933/20000000000000000000)
  directionLo := (17544549326576170559/4000000000000000000)
  directionHi := (54826716645550532997/12500000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree082.table
  base := (-4295739233672964000864260813294165171483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-28064617591500194954123869758640000000000000)
      constant := (418665403162869965896422844178381931327207065) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree082.table
  base := (-17183532575093802923503246555558159017/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (133518)
      previous := (87567)
      next := (0)
      square := (2080518962420461541798499788025000000000000)
      linear := (-128966897670276019982615876386320000000000000)
      constant := (1966076239242687237754929002518564767747989375) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17544549326576170559/4000000000000000000)
  centralHi := (54826716645550532997/12500000000000000000)
  directionLo := (441312920075546322467/100000000000000000000)
  directionHi := (110328230018886580617/25000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree083.table
  base := (-4072218329364031903550021450092540884461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-28423609098741372631924395212260000000000000)
      constant := (429953752521231500602568936199618278421953855) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree083.table
  base := (-4072346863559391869719341384053905606601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (267036)
      previous := (175134)
      next := (0)
      square := (4161037924840923083596999576050000000000000)
      linear := (-261229990088857398643218395574060000000000000)
      constant := (4037874356688715866488322341844436957586153995) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (441312920075546322467/100000000000000000000)
  centralHi := (110328230018886580617/25000000000000000000)
  directionLo := (88799139619885022341/20000000000000000000)
  directionHi := (221997849049712555853/50000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree084.table
  base := (-3842449431523649535181079863355244045559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-28782600605982550309724920665880000000000000)
      constant := (441390503403645496990005747521739672354167245) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree084.table
  base := (-960641054009448814449108611315206184817/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (44506)
      previous := (29189)
      next := (0)
      square := (693506320806820513932833262675000000000000)
      linear := (-44087697472860459553534173062580000000000000)
      constant := (690830503424049834401915175681849162377636610) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (88799139619885022341/20000000000000000000)
  centralHi := (221997849049712555853/50000000000000000000)
  directionLo := (446662362905121164373/100000000000000000000)
  directionHi := (223331181452560582187/50000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree085.table
  base := (-450804217342101153359524467483974757777/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 25000000000000000000000000000000000000000
      center := (52)
      previous := (33)
      next := (0)
      square := (799891950180877178699923025000000000000)
      linear := (-50417979434643128006099387750000000000000)
      constant := (783694903249405953529873132175320504844460) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree085.table
  base := (-3606536229946746968966901093573099424913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 450000000000000000000000000000000000000000
      center := (924)
      previous := (606)
      next := (0)
      square := (14398055103255789216598614450000000000000)
      linear := (-926721036627917356398587132100000000000000)
      constant := (14717918535202024518646426675439210525878915) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (446662362905121164373/100000000000000000000)
  centralHi := (223331181452560582187/50000000000000000000)
  directionLo := (449313201387602755341/100000000000000000000)
  directionHi := (224656600693801377671/50000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree086.table
  base := (-841043078463357191892317673893470683179/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-14750291810232452832662985786560000000000000)
      constant := (232354601504473400924171108495691869725612690) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree086.table
  base := (-420532976968399732837842542534119774791/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (133518)
      previous := (87567)
      next := (0)
      square := (2080518962420461541798499788025000000000000)
      linear := (-135559287166886737338589161989160000000000000)
      constant := (2181680326617714719496433880017611089315372180) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449313201387602755341/100000000000000000000)
  centralHi := (224656600693801377671/50000000000000000000)
  directionLo := (225974246013990929527/50000000000000000000)
  directionHi := (90389698405596371811/20000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree087.table
  base := (-48682282808025832111081446907652192687/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-14929787563853041671563248513370000000000000)
      constant := (238295574416805984723920357714691162610153120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree087.table
  base := (-3115747779591102153827611380180988215219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (89012)
      previous := (58378)
      next := (0)
      square := (1387012641613641027865666525350000000000000)
      linear := (-91471589694026277785054988926580000000000000)
      constant := (1491543199915475300386620239587441416087025635) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (225974246013990929527/50000000000000000000)
  centralHi := (90389698405596371811/20000000000000000000)
  directionLo := (113642126308743089881/25000000000000000000)
  directionHi := (18182740209398894381/4000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree088.table
  base := (-286091593304360530489588732670870570231/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-15109283317473630510463511240180000000000000)
      constant := (244310745171541448379754679766548960130081025) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree088.table
  base := (-2860988835631846309023778022601790409167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (267036)
      previous := (175134)
      next := (0)
      square := (4161037924840923083596999576050000000000000)
      linear := (-277710963830384192033151609581160000000000000)
      constant := (4587285286918809681390593344543231715728783165) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113642126308743089881/25000000000000000000)
  centralHi := (18182740209398894381/4000000000000000000)
  directionLo := (457173503668735601893/100000000000000000000)
  directionHi := (228586751834367800947/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree089.table
  base := (-519984511346930689663398975584780191869/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-30577558142188438698727547933980000000000000)
      constant := (500800226463881556255492922790257963113746475) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree089.table
  base := (-1299993808436961432344832771965126302267/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (133518)
      previous := (87567)
      next := (0)
      square := (2080518962420461541798499788025000000000000)
      linear := (-140503579289344775355569126191290000000000000)
      constant := (2350663853260178677124602058329214532439017665) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457173503668735601893/100000000000000000000)
  centralHi := (228586751834367800947/50000000000000000000)
  directionLo := (91952748509642215319/20000000000000000000)
  directionHi := (114940935637052769149/25000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree090.table
  base := (-2332686630694448446970586213440935248793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-30936549649429616376528073387600000000000000)
      constant := (513127356242441392585282221566977848565494115) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree090.table
  base := (-1166372342367698638710708478180275303881/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (44506)
      previous := (29189)
      next := (0)
      square := (693506320806820513932833262675000000000000)
      linear := (-47383892221165818231520815864000000000000000)
      constant := (802792808541637829745443365872388506557675865) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91952748509642215319/20000000000000000000)
  centralHi := (114940935637052769149/25000000000000000000)
  directionLo := (46233946994295006619/10000000000000000000)
  directionHi := (462339469942950066191/100000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree091.table
  base := (-2059208741436048457855042491869018042207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-31295541156670794054328598841220000000000000)
      constant := (525602878831251036712014595089067268929010885) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree091.table
  base := (-205926053747609115933594077932595677587/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (133518)
      previous := (87567)
      next := (0)
      square := (2080518962420461541798499788025000000000000)
      linear := (-143799774037650134033555768992710000000000000)
      constant := (2466786357313674786997690592487853966064905325) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46233946994295006619/10000000000000000000)
  centralHi := (462339469942950066191/100000000000000000000)
  directionLo := (464900927050396769909/100000000000000000000)
  directionHi := (46490092705039676991/10000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree092.table
  base := (-222436176319009964318925088714584137541/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-15827266331955985866064562147420000000000000)
      constant := (269113396738304571864082722448285703685013020) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree092.table
  base := (-1779535617626231643238755959979733079313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (267036)
      previous := (175134)
      next := (0)
      square := (4161037924840923083596999576050000000000000)
      linear := (-290895742823605626745098180786840000000000000)
      constant := (5051775290897819536955231311974831571303534435) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (464900927050396769909/100000000000000000000)
  centralHi := (46490092705039676991/10000000000000000000)
  directionLo := (233724174229747066251/50000000000000000000)
  directionHi := (467448348459494132503/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree093.table
  base := (-149352910220376207353900919250419832793/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-16006762085576574704964824874230000000000000)
      constant := (275499549753901375470561056329556716708070575) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree093.table
  base := (-746785159267151437946886953348991621587/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (44506)
      previous := (29189)
      next := (0)
      square := (693506320806820513932833262675000000000000)
      linear := (-49031989595318497570514137264710000000000000)
      constant := (861894095824289971837257651394295121320420355) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (233724174229747066251/50000000000000000000)
  centralHi := (467448348459494132503/100000000000000000000)
  directionLo := (14686936325044680843/3125000000000000000)
  directionHi := (469981962401429786977/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree094.table
  base := (-1501660287174381883004067067066634761/12500000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-16186257839197163543865087601040000000000000)
      constant := (281959898163771702970971858010399485108142000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree094.table
  base := (-600682495069362536848271942118455604319/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (133518)
      previous := (87567)
      next := (0)
      square := (2080518962420461541798499788025000000000000)
      linear := (-148744066160108172050535733194840000000000000)
      constant := (2646170281110080650643050427980185484865831405) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14686936325044680843/3125000000000000000)
  centralHi := (469981962401429786977/100000000000000000000)
  directionLo := (236250995494140338107/50000000000000000000)
  directionHi := (94500398197656135243/20000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree095.table
  base := (-451443580772211057063334847611525416551/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-16365753592817752382765350327850000000000000)
      constant := (288494441701757310872355245518326345773083805) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree095.table
  base := (-1444671910488884827757843674260502483/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (267036)
      previous := (175134)
      next := (0)
      square := (4161037924840923083596999576050000000000000)
      linear := (-300784327068521702779058109191100000000000000)
      constant := (5414703248668517155319872023577001353255365625) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (236250995494140338107/50000000000000000000)
  centralHi := (94500398197656135243/20000000000000000000)
  directionLo := (95001730088052519587/20000000000000000000)
  directionHi := (29688040652516412371/6250000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree096.table
  base := (-23928249048411730861349468675400109447/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-33090498692876682443331226109320000000000000)
      constant := (590206360260901274262801064974149171046227125) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree096.table
  base := (-598235458063430010999101419807567459399/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (89012)
      previous := (58378)
      next := (0)
      square := (1387012641613641027865666525350000000000000)
      linear := (-101360173938942353819014917330840000000000000)
      constant := (1846150876892765378984800545536238195063505335) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95001730088052519587/20000000000000000000)
  centralHi := (29688040652516412371/6250000000000000000)
  directionLo := (119375537825560679281/25000000000000000000)
  directionHi := (3820017210417941737/800000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree097.table
  base := (-287285717105101756118760287175940372531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-33449490200117860121131751562940000000000000)
      constant := (603572226475786628382736166286752766161692705) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree097.table
  base := (-287311780057379570527965226733481316481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (267036)
      previous := (175134)
      next := (0)
      square := (4161037924840923083596999576050000000000000)
      linear := (-307376716565132420135031394793940000000000000)
      constant := (5663588705025623465365669333045589075479164595) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119375537825560679281/25000000000000000000)
  centralHi := (3820017210417941737/800000000000000000)
  directionLo := (119995674662532161521/25000000000000000000)
  directionHi := (95996539730025729217/20000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree098.table
  base := (5974820717595205075164556899143543511/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-33808481707359037798932277016560000000000000)
      constant := (617086481669315994196772973784868312101866975) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree098.table
  base := (186567927909308198617535993664339233/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (133518)
      previous := (87567)
      next := (0)
      square := (2080518962420461541798499788025000000000000)
      linear := (-155336455656718889406509018797680000000000000)
      constant := (2895055734414964619054498163162652378538013200) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119995674662532161521/25000000000000000000)
  centralHi := (95996539730025729217/20000000000000000000)
  directionLo := (241225246143853338089/50000000000000000000)
  directionHi := (482450492287706676179/100000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree099.table
  base := (353273001300363867522900692201038492797/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-34167473214600215476732802470180000000000000)
      constant := (630749125502537779088069310908928500622091665) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree099.table
  base := (88313072333195727601194331040110839739/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (44506)
      previous := (29189)
      next := (0)
      square := (693506320806820513932833262675000000000000)
      linear := (-52328184343623856248500780066130000000000000)
      constant := (986336819918996912464006898250884760980537130) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (241225246143853338089/50000000000000000000)
  centralHi := (482450492287706676179/100000000000000000000)
  directionLo := (484905726934463860689/100000000000000000000)
  directionHi := (48490572693446386069/10000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree100.table
  base := (5335240358766442636767113050582409447/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-17263232360920696577266663961900000000000000)
      constant := (322280078835921547514302824386917861225658560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree100.table
  base := (682892304987153700524120487138598076469/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (267036)
      previous := (175134)
      next := (0)
      square := (4161037924840923083596999576050000000000000)
      linear := (-317265300810048496168991323198200000000000000)
      constant := (6047317054768646870830444616679237467984479345) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (484905726934463860689/100000000000000000000)
  centralHi := (48490572693446386069/10000000000000000000)
  directionLo := (243674296202446813319/50000000000000000000)
  directionHi := (487348592404893626639/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree101.table
  base := (1018787209011898245842347050382458037287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-34885456229082570832333853377420000000000000)
      constant := (658519577904934263302378553754980651863879715) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree101.table
  base := (1018770756097005305555058466472624461931/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (267036)
      previous := (175134)
      next := (0)
      square := (4161037924840923083596999576050000000000000)
      linear := (-320561495558353854846977965999620000000000000)
      constant := (6177999872521818015370760000804358481127412655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (243674296202446813319/50000000000000000000)
  centralHi := (487348592404893626639/100000000000000000000)
  directionLo := (61222409222469024031/12500000000000000000)
  directionHi := (489779273779752192249/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree102.table
  base := (1360902161330566812481491604218356532473/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (104)
      previous := (66)
      next := (0)
      square := (1599783900361754357399846050000000000000)
      linear := (-121953106354061413529876743360000000000000)
      constant := (2327430401236196096745383913309091782662365) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree102.table
  base := (340221874862385813668145663578231817133/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 75000000000000000000000000000000000000000
      center := (154)
      previous := (101)
      next := (0)
      square := (2399675850542631536099769075000000000000)
      linear := (-186769140891960330752574745560000000000000)
      constant := (3639025012059407448853464997079346954513990) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61222409222469024031/12500000000000000000)
  centralHi := (489779273779752192249/100000000000000000000)
  directionLo := (492197951569703065851/100000000000000000000)
  directionHi := (123049487892425766463/25000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree103.table
  base := (213656933832539596018851527324765731099/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-17801719621782463093967452142330000000000000)
      constant := (343441790804433804631609313566518145925752220) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree103.table
  base := (1709242406092661858546670505275965977201/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (267036)
      previous := (175134)
      next := (0)
      square := (4161037924840923083596999576050000000000000)
      linear := (-327153885054964572202951251602460000000000000)
      constant := (6443525548259208239164152585870211937533499005) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (492197951569703065851/100000000000000000000)
  centralHi := (123049487892425766463/25000000000000000000)
  directionLo := (98920960374351820407/20000000000000000000)
  directionHi := (123651200467939775509/25000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree104.table
  base := (1031923499938274439639916370180661566619/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-17981215375403051932867714869140000000000000)
      constant := (350644082330805014660638622136895055963764455) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree104.table
  base := (515958839924034749403998725997234245801/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (133518)
      previous := (87567)
      next := (0)
      square := (2080518962420461541798499788025000000000000)
      linear := (-165225039901634965440468947201940000000000000)
      constant := (3289184201526765322631298892236404062733284010) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98920960374351820407/20000000000000000000)
  centralHi := (123651200467939775509/25000000000000000000)
  directionLo := (248499998259452905143/50000000000000000000)
  directionHi := (496999996518905810287/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree105.table
  base := (2424676625242840399286677504790461754309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-36321422258047281543535955191900000000000000)
      constant := (715841134936688801264780992033072217234976505) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree105.table
  base := (48493325102122378086094445400350048531/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (44506)
      previous := (29189)
      next := (0)
      square := (693506320806820513932833262675000000000000)
      linear := (-55624379091929214926487422867550000000000000)
      constant := (1119099655654408973391653364171637936509547125) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (248499998259452905143/50000000000000000000)
  centralHi := (496999996518905810287/100000000000000000000)
  directionLo := (15605740725727052683/3125000000000000000)
  directionHi := (499383703223265685857/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree106.table
  base := (2791744234903144008439623647738803094253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-36680413765288459221336480645520000000000000)
      constant := (730542492272471936716717530872190570471195585) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree106.table
  base := (2791734997069954350202575941152090198789/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (267036)
      previous := (175134)
      next := (0)
      square := (4161037924840923083596999576050000000000000)
      linear := (-337042469299880648236911180006720000000000000)
      constant := (6852214139639217147220644139549234933035250945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (15605740725727052683/3125000000000000000)
  centralHi := (499383703223265685857/100000000000000000000)
  directionLo := (125439021428285278013/25000000000000000000)
  directionHi := (501756085713141112053/100000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree107.table
  base := (395631215943533857366307187705539360723/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-18519702636264818449568503049570000000000000)
      constant := (372696118261283828896001996020759017504978940) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree107.table
  base := (791260374777800894647297333369230170811/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (133518)
      previous := (87567)
      next := (0)
      square := (2080518962420461541798499788025000000000000)
      linear := (-170169332024093003457448911404070000000000000)
      constant := (3495608509533597220414310640303602676742794110) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (125439021428285278013/25000000000000000000)
  centralHi := (501756085713141112053/100000000000000000000)
  directionLo := (20164692154570109253/4000000000000000000)
  directionHi := (252058651932126365663/50000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree108.table
  base := (3544593011236395419442355734757531582129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-37398396779770814576937531552760000000000000)
      constant := (760390367554120026597887565826676633136176405) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree108.table
  base := (88614642063424437982026029246337750453/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (44506)
      previous := (29189)
      next := (0)
      square := (693506320806820513932833262675000000000000)
      linear := (-57272476466081894265480744268260000000000000)
      constant := (1188601095197830783136019152332425482964275100) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20164692154570109253/4000000000000000000)
  centralHi := (252058651932126365663/50000000000000000000)
  directionLo := (126616878456367743753/25000000000000000000)
  directionHi := (506467513825470975013/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree109.table
  base := (982593500587419783460119966116993343237/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-18878694143505996127369028503190000000000000)
      constant := (387768442623150633210376705310147110761954930) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree109.table
  base := (982591868890486941044527178396679653387/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (133518)
      previous := (87567)
      next := (0)
      square := (2080518962420461541798499788025000000000000)
      linear := (-173465526772398362135435554205490000000000000)
      constant := (3636691397532509862617892122010278637784595870) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (126616878456367743753/25000000000000000000)
  centralHi := (506467513825470975013/100000000000000000000)
  directionLo := (254403434069660282483/50000000000000000000)
  directionHi := (508806868139320564967/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree110.table
  base := (216119631233559719624802224429341791689/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-19058189897126584966269291230000000000000000)
      constant := (395415894744488958432343965758103988889906050) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree110.table
  base := (1080596703133797343142444671863026465107/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (133518)
      previous := (87567)
      next := (0)
      square := (2080518962420461541798499788025000000000000)
      linear := (-175113624146551041474428875606200000000000000)
      constant := (3708272844923754620616843872507457318357433070) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254403434069660282483/50000000000000000000)
  centralHi := (508806868139320564967/100000000000000000000)
  directionLo := (511135515857521151039/100000000000000000000)
  directionHi := (1597298487054753597/312500000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree111.table
  base := (4720648808568171981004790647858917339109/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-38475371301494347610339107913620000000000000)
      constant := (806275080181530626414876974318294135555012505) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree111.table
  base := (2360321816628837345033674705031053668873/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (44506)
      previous := (29189)
      next := (0)
      square := (693506320806820513932833262675000000000000)
      linear := (-58920573840234573604474065668970000000000000)
      constant := (1260182542458594148694083391935196617654564455) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (511135515857521151039/100000000000000000000)
  centralHi := (1597298487054753597/312500000000000000)
  directionLo := (513453602651811731811/100000000000000000000)
  directionHi := (128363400662952932953/25000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree112.table
  base := (5125142490269222308330969535021017735169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-38834362808735525288139633367240000000000000)
      constant := (821866757231809737112273882000057370627319205) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree112.table
  base := (205005515295187253122622903689189722177/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (267036)
      previous := (175134)
      next := (0)
      square := (4161037924840923083596999576050000000000000)
      linear := (-356819637789712800304831036815240000000000000)
      constant := (7707031489057363538364410809808475808422797125) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (513453602651811731811/100000000000000000000)
  centralHi := (128363400662952932953/25000000000000000000)
  directionLo := (515761270920292035543/100000000000000000000)
  directionHi := (64470158865036504443/12500000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree113.table
  base := (5535873611224618317716187800508444040067/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-39193354315976702965940158820860000000000000)
      constant := (837606820555210893359862776171376701637896815) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree113.table
  base := (5535869508868652457254774146052411978901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (267036)
      previous := (175134)
      next := (0)
      square := (4161037924840923083596999576050000000000000)
      linear := (-360115832538018158982817679616660000000000000)
      constant := (7854354392101226778268246808093629617785607505) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (515761270920292035543/100000000000000000000)
  centralHi := (64470158865036504443/12500000000000000000)
  directionLo := (259029329944750267421/50000000000000000000)
  directionHi := (518058659889500534843/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree114.table
  base := (2976421058769999065167122960068862634127/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-19776172911608940321870342137240000000000000)
      constant := (426747635036928371121369899259903506506313515) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree114.table
  base := (5952838465539171057351542728133796316951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (89012)
      previous := (58378)
      next := (0)
      square := (1387012641613641027865666525350000000000000)
      linear := (-121137342428774505886934774139360000000000000)
      constant := (2667687987756502754509074193981924007033982585) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259029329944750267421/50000000000000000000)
  centralHi := (518058659889500534843/100000000000000000000)
  directionLo := (520345905712436159387/100000000000000000000)
  directionHi := (130086476428109039847/25000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree115.table
  base := (398502997467185479526643157271237582481/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-19955668665229529160770604864050000000000000)
      constant := (434766052857936207162161702957380506453480360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree115.table
  base := (1594011177159424936269456491159006554777/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (133518)
      previous := (87567)
      next := (0)
      square := (2080518962420461541798499788025000000000000)
      linear := (-183354111017314438169395482609750000000000000)
      constant := (4076580100996596620235903530121570760489749770) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (520345905712436159387/100000000000000000000)
  centralHi := (130086476428109039847/25000000000000000000)
  directionLo := (104524628312543797947/20000000000000000000)
  directionHi := (65327892695339873717/12500000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree116.table
  base := (106335798296860547304070212652891926249/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-20135164418850117999670867590860000000000000)
      constant := (442858663707371953292612553463053722669753760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree116.table
  base := (1701372049368902535535159018638658823277/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (133518)
      previous := (87567)
      next := (0)
      square := (2080518962420461541798499788025000000000000)
      linear := (-185002208391467117508388804010460000000000000)
      constant := (4152321553871563048521149968446887515993434770) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104524628312543797947/20000000000000000000)
  centralHi := (65327892695339873717/12500000000000000000)
  directionLo := (524890497725074200611/100000000000000000000)
  directionHi := (131222624431268550153/25000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree117.table
  base := (226286608418703258237861029023068419661/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-20314660172470706838571130317670000000000000)
      constant := (451025467554374877501978669885594341862562320) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree117.table
  base := (3620584447052397213523952362722137149937/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (44506)
      previous := (29189)
      next := (0)
      square := (693506320806820513932833262675000000000000)
      linear := (-62216768588539932282460708470390000000000000)
      constant := (1409585446670965281836699477205703464544976895) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (524890497725074200611/100000000000000000000)
  centralHi := (131222624431268550153/25000000000000000000)
  directionLo := (263574050841156609099/50000000000000000000)
  directionHi := (527148101682313218199/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree118.table
  base := (480193065932975654208451630682907588889/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-20494155926091295677471393044480000000000000)
      constant := (459266464370228751340224337103810411727556840) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree118.table
  base := (768308676303082905959665474803693708627/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (133518)
      previous := (87567)
      next := (0)
      square := (2080518962420461541798499788025000000000000)
      linear := (-188298403139772476186375446811880000000000000)
      constant := (4305884459189792522132579060589074183403470675) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (263574050841156609099/50000000000000000000)
  centralHi := (527148101682313218199/100000000000000000000)
  directionLo := (13234901954974410279/2500000000000000000)
  directionHi := (529396078198976411161/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree119.table
  base := (8131243810500101552340731846945971944601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 50000000000000000000000000000000000000000
      center := (104)
      previous := (66)
      next := (0)
      square := (1599783900361754357399846050000000000000)
      linear := (-143070253838836571047554711220000000000000)
      constant := (3235859198118607119550203914636729859723005) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree119.table
  base := (8131241770959257530874346446021561614319/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 450000000000000000000000000000000000000000
      center := (924)
      previous := (606)
      next := (0)
      square := (14398055103255789216598614450000000000000)
      linear := (-1314508654075606612632309814620000000000000)
      constant := (30337065129313189445947322255968970272644355) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13234901954974410279/2500000000000000000)
  centralHi := (529396078198976411161/100000000000000000000)
  directionLo := (531634549401792602141/100000000000000000000)
  directionHi := (265817274700896301071/50000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree120.table
  base := (2146408925353819152840614732376483346823/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-20853147433332473355271918498100000000000000)
      constant := (475971036803033553400819651428568036872318470) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree120.table
  base := (1717126777314216988072324844266110572647/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (89012)
      previous := (58378)
      next := (0)
      square := (1387012641613641027865666525350000000000000)
      linear := (-127729731925385223242908059742200000000000000)
      constant := (2974813797198089426393265558690667946662123725) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (531634549401792602141/100000000000000000000)
  centralHi := (265817274700896301071/50000000000000000000)
  directionLo := (533863634857102221639/100000000000000000000)
  directionHi := (13346590871427555541/2500000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree121.table
  base := (904626469511526441381112360791681941531/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-21032643186953062194172181224910000000000000)
      constant := (484434612371390163253569136899068902027561475) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree121.table
  base := (9046263080324040663921512347735436026507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (267036)
      previous := (175134)
      next := (0)
      square := (4161037924840923083596999576050000000000000)
      linear := (-386485390524461028406710822028020000000000000)
      constant := (9082857625663657402701318384149461345524723535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (533863634857102221639/100000000000000000000)
  centralHi := (13346590871427555541/2500000000000000000)
  directionLo := (268041725822691494651/50000000000000000000)
  directionHi := (536083451645382989303/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree122.table
  base := (9513130760969677322708585719612322357463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-42424277881147302066144887903440000000000000)
      constant := (985944761622156206531072431618111805806534035) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree122.table
  base := (9513129324276573778953629374023157297647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (267036)
      previous := (175134)
      next := (0)
      square := (4161037924840923083596999576050000000000000)
      linear := (-389781585272766387084697464829440000000000000)
      constant := (9242660524216299250694923295434379160655899235) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268041725822691494651/50000000000000000000)
  centralHi := (536083451645382989303/100000000000000000000)
  directionLo := (538294114433009561843/100000000000000000000)
  directionHi := (134573528608252390461/25000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree123.table
  base := (4993116935042256325665352090353292120529/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-21391634694194239871972706678530000000000000)
      constant := (501584342101221456495562696225421507114164405) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree123.table
  base := (9986232591931905799845011483849450866393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (89012)
      previous := (58378)
      next := (0)
      square := (1387012641613641027865666525350000000000000)
      linear := (-131025926673690581920894702543620000000000000)
      constant := (3134616695635867739651738271831733369505813655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (538294114433009561843/100000000000000000000)
  centralHi := (134573528608252390461/25000000000000000000)
  directionLo := (540495735541371597691/100000000000000000000)
  directionHi := (135123933885342899423/25000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree124.table
  base := (10465573995132501701973480246438505340011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-43142260895629657421745938810680000000000000)
      constant := (1020540992444152542619114878110151640216315895) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree124.table
  base := (10465572858099782414242491946892951319553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (267036)
      previous := (175134)
      next := (0)
      square := (4161037924840923083596999576050000000000000)
      linear := (-396373974769377104440670750432280000000000000)
      constant := (9566426313409970050150040011004094831910786765) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (540495735541371597691/100000000000000000000)
  centralHi := (135123933885342899423/25000000000000000000)
  directionLo := (271344212506734062421/50000000000000000000)
  directionHi := (542688425013468124843/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree125.table
  base := (5475575555101216039545706368031425155437/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-21750626201435417549773232132150000000000000)
      constant := (519030843154921696751738819694930409349606465) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree125.table
  base := (2190230019754769075886612109916724618327/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (267036)
      previous := (175134)
      next := (0)
      square := (4161037924840923083596999576050000000000000)
      linear := (-399670169517682463118657393233700000000000000)
      constant := (9730389203411197055332916184133585018306713175) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271344212506734062421/50000000000000000000)
  centralHi := (542688425013468124843/100000000000000000000)
  directionLo := (544872290678089930831/100000000000000000000)
  directionHi := (34054518167380620677/6250000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree126.table
  base := (2860741297666314085232871145502424868201/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-21930121955056006388673494858960000000000000)
      constant := (527865382881963246045440283313666007869100890) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree126.table
  base := (572148214551139600753494238226306117361/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 21675000000000000000000000000000000000000000
      center := (44506)
      previous := (29189)
      next := (0)
      square := (693506320806820513932833262675000000000000)
      linear := (-67161060710997970299440672672520000000000000)
      constant := (1649289792768843773857655462977482370187599350) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (544872290678089930831/100000000000000000000)
  centralHi := (34054518167380620677/6250000000000000000)
  directionLo := (547047438211695895657/100000000000000000000)
  directionHi := (273523719105847947829/50000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree127.table
  base := (11941016213055054060116552768415350563609/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-44219235417353190455147515171540000000000000)
      constant := (1073548230772493583363763688164642181564415005) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree127.table
  base := (5970507706446853379191552279203648798453/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 65025000000000000000000000000000000000000000
      center := (133518)
      previous := (87567)
      next := (0)
      square := (2080518962420461541798499788025000000000000)
      linear := (-203131279507146590237315339418270000000000000)
      constant := (5031237486365034573347633881232392452623881265) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (547047438211695895657/100000000000000000000)
  centralHi := (273523719105847947829/50000000000000000000)
  directionLo := (68651746399760466847/12500000000000000000)
  directionHi := (549213971198083734777/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree128.table
  base := (6222652077481569401335620954917112264127/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7225000000000000000000000000000000000000000
      center := (15028)
      previous := (9537)
      next := (0)
      square := (231168773602273504644277754225000000000000)
      linear := (-22289113462297184066474020312580000000000000)
      constant := (545757040651582057712516293284911227221663515) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree128.table
  base := (12445303443326140506647266216033385599809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 130050000000000000000000000000000000000000000
      center := (267036)
      previous := (175134)
      next := (0)
      square := (4161037924840923083596999576050000000000000)
      linear := (-409558753762598539152617321637960000000000000)
      constant := (10230597851488325425399976612367162179725516045) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell018.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (68651746399760466847/12500000000000000000)
  centralHi := (549213971198083734777/100000000000000000000)
  directionLo := (551371991185950487061/100000000000000000000)
  directionHi := (275685995592975243531/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 33
  qDenominator := 85
  table := BinomialMassData.Q33_85.Degree129.table
  base := (12955828994943799850870391276681619596433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 14450000000000000000000000000000000000000000
      center := (30056)
      previous := (19074)
      next := (0)
      square := (462337547204547009288555508450000000000000)
      linear := (-44937218431835545810748566078780000000000000)
      constant := (1109628317324949036287574404588622940316845685) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q33_85.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 101
  qDenominator := 255
  table := BinomialMassData.Q101_255.Degree129.table
  base := (12955828362075682021731559264144591292687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 43350000000000000000000000000000000000000000
      center := (89012)
      previous := (58378)
      next := (0)
      square := (1387012641613641027865666525350000000000000)
      linear := (-137618316170301299276867988146460000000000000)
      constant := (3466702464208184303702722712455760803253798145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q101_255.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell018.Kernel129
