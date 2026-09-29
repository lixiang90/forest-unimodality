import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell103.Parameters
import ForestUnimodality.BinomialMassData.Q22597_43472.Batch000_049
import ForestUnimodality.BinomialMassData.Q22597_43472.Batch050_099
import ForestUnimodality.BinomialMassData.Q22597_43472.Batch100_149
import ForestUnimodality.BinomialMassData.Q11311_21736.Batch000_049
import ForestUnimodality.BinomialMassData.Q11311_21736.Batch050_099
import ForestUnimodality.BinomialMassData.Q11311_21736.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree000.table
  base := (6092452981606458355500421957/100000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (122)
      previous := (61)
      next := (61)
      square := (786339352022524668006653310000000000000)
      linear := (-31537512552701884444017466000000000000)
      constant := (609245298160645835550042195700000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree000.table
  base := (6092452981606458355500421957/100000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (122)
      previous := (61)
      next := (61)
      square := (786339352022524668006653310000000000000)
      linear := (-31537512552701884444017466000000000000)
      constant := (609245298160645835550042195700000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree001.table
  base := (41544668110976074145033775617363222474961/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-6267578897928059204014104819912997750000000000)
      constant := (2455180970568452445818297691516917471025386488232) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree001.table
  base := (332051807883168127635407686188273188706571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-6274255410488825452523398810673216500000000000)
      constant := (2452929075504073506702885859787073686064452006819) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (9991688896166689071/20000000000000000000)
  directionHi := (12489611120208361339/25000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree002.table
  base := (95880093683502048168614971992983233875209/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-12302345071353455906594757188259521500000000000)
      constant := (1422106618178464512106107904145697004417965463202) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree002.table
  base := (47862700552815528115320875133151591349679/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-12315698096474988403613345169779959000000000000)
      constant := (1419836866836987369875088669659707358714841997724) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9991688896166689071/20000000000000000000)
  centralHi := (12489611120208361339/25000000000000000000)
  directionLo := (35325954869928977883/50000000000000000000)
  directionHi := (70651909739857955767/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree003.table
  base := (59287429538837706356614306440659317376363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-18337111244778852609175409556606045250000000000)
      constant := (889809295600688450067917106336247638720303824614) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree003.table
  base := (118334450411468548437845100390323171787923/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-18357140782461151354703291528886701500000000000)
      constant := (888066230780834045737797635601168942869486711147) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35325954869928977883/50000000000000000000)
  centralHi := (70651909739857955767/100000000000000000000)
  directionLo := (43265282053956244873/50000000000000000000)
  directionHi := (86530564107912489747/100000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree004.table
  base := (78995792723466652719859551375463593090583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-24371877418204249311756061924952569000000000000)
      constant := (608733296357935707235575743934007855829468767887) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree004.table
  base := (39411895831348528120024345290113160802823/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-24398583468447314305793237887993444000000000000)
      constant := (607519663326811277069779532686088944735501674494) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43265282053956244873/50000000000000000000)
  centralHi := (86530564107912489747/100000000000000000000)
  directionLo := (99916888961666890711/100000000000000000000)
  directionHi := (12489611120208361339/12500000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree005.table
  base := (28195379280350059388456783559738387254897/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-30406643591629646014336714293299092750000000000)
      constant := (456098020213930332756894920401097438606418179666) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree005.table
  base := (11253885194662590272041927089224289247371/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-30440026154433477256883184247100186500000000000)
      constant := (455289811940072567348385196567867133897928690095) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99916888961666890711/100000000000000000000)
  centralHi := (12489611120208361339/12500000000000000000)
  directionLo := (11171047790929277323/10000000000000000000)
  directionHi := (111710477909292773231/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree006.table
  base := (42539065179372280595777505854931655257901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-36441409765055042716917366661645616500000000000)
      constant := (371217591538490775727136644431082788749893135189) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree006.table
  base := (21225671488597634951479262867202814931273/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-36481468840419640207973130606206929000000000000)
      constant := (370695828516990376332210960258983215121372338594) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11171047790929277323/10000000000000000000)
  centralHi := (111710477909292773231/100000000000000000000)
  directionLo := (61186348660602199773/50000000000000000000)
  directionHi := (122372697321204399547/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree007.table
  base := (8337912288471817660068854044694282685771/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-42476175938480439419498019029992140250000000000)
      constant := (323906180197223463962039323106965780614769722476) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree007.table
  base := (33285197505090647670471420337616944985191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-42522911526405803159063076965313671500000000000)
      constant := (323586713511416305963506884173394675507533643999) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61186348660602199773/50000000000000000000)
  centralHi := (122372697321204399547/100000000000000000000)
  directionLo := (33044404995978161963/25000000000000000000)
  directionHi := (132177619983912647853/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree008.table
  base := (13385476657255481006004550781130836672141/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-48510942111905836122078671398338664000000000000)
      constant := (298974716040562966360333512214011578416417365098) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree008.table
  base := (6679461172969194649776308279321166328679/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-48564354212391966110153023324420414000000000000)
      constant := (298805968799124496995220042202244289688446521724) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33044404995978161963/25000000000000000000)
  centralHi := (132177619983912647853/100000000000000000000)
  directionLo := (141303819479715911533/100000000000000000000)
  directionHi := (70651909739857955767/50000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree009.table
  base := (21742440629711581923266943925011296274089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-54545708285331232824659323766685187750000000000)
      constant := (288638512847945929875353940748890258405380891921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree009.table
  base := (1356119071854817765903292611488537894037/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-54605796898378129061242969683527156500000000000)
      constant := (288592218166044526409075214235638777637209252688) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141303819479715911533/100000000000000000000)
  centralHi := (70651909739857955767/50000000000000000000)
  directionLo := (149875333442500336067/100000000000000000000)
  directionHi := (37468833360625084017/25000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree010.table
  base := (4427478496589569616707926815149921307563/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-60580474458756629527239976135031711500000000000)
      constant := (288791674028697337082203230178158196460455756428) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree010.table
  base := (17671192945511418377205050770620929130267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-60647239584364292012332916042633899000000000000)
      constant := (288854411732368919285838383485311758477323587763) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149875333442500336067/100000000000000000000)
  centralHi := (37468833360625084017/25000000000000000000)
  directionLo := (78991236459250935969/50000000000000000000)
  directionHi := (157982472918501871939/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree011.table
  base := (14367304547984092746630758516927502077131/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (7443098)
      previous := (3721549)
      next := (3721549)
      square := (47973777527542207470417911789790000000000000)
      linear := (-550539178778363853139013458705605250000000000)
      constant := (2455989852825550841741582254932863153911185179) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree011.table
  base := (7166417481449838223451153669581788606487/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (7443098)
      previous := (3721549)
      next := (3721549)
      square := (47973777527542207470417911789790000000000000)
      linear := (-551146134465706239367131094229261500000000000)
      constant := (2457371479492017994431167498615628900936330766) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78991236459250935969/50000000000000000000)
  centralHi := (157982472918501871939/100000000000000000000)
  directionLo := (82846707726363054179/50000000000000000000)
  directionHi := (165693415452726108359/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree012.table
  base := (5768090804973875097128077530903276314759/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-72650006805607422932401280871724759000000000000)
      constant := (312470615995534272243514587937337479669285903102) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree012.table
  base := (719067335496240072305068200781354509087/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-72730124956336617914512808760847384000000000000)
      constant := (312742635402584391492744647173719816926104683888) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82846707726363054179/50000000000000000000)
  centralHi := (165693415452726108359/100000000000000000000)
  directionLo := (43265282053956244873/25000000000000000000)
  directionHi := (173061128215824979493/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree013.table
  base := (4552483068926798490880439749390466748193/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34348089235695900023198623234110000000000000)
      linear := (-465590372656998932751372386035924750000000000)
      constant := (1975476444243682961476077312096778385743136866) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree013.table
  base := (9076709109196134821417058450006266381593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34348089235695900023198623234110000000000000)
      linear := (-466103950546288644175164231479018500000000000)
      constant := (1977724858017970846895428322915173440564363833) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43265282053956244873/25000000000000000000)
  centralHi := (173061128215824979493/100000000000000000000)
  directionLo := (22515966652258240663/12500000000000000000)
  directionHi := (36025546643613185061/20000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree014.table
  base := (1399697306348274906007302591836210065111/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-84719539152458216337562585608417806500000000000)
      constant := (360774557995657071294566997530132387085475984395) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree014.table
  base := (6972751312890933153467673859099618177411/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-84813010328308943816692701479060869000000000000)
      constant := (361267045106546033528409943952083551626665791579) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22515966652258240663/12500000000000000000)
  centralHi := (36025546643613185061/20000000000000000000)
  directionLo := (93463691411723151997/50000000000000000000)
  directionHi := (37385476564689260799/20000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree015.table
  base := (2581250601465644987409246765873062356777/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-90754305325883613040143237976764330250000000000)
      constant := (392827316515822601233278467719730830970242634306) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree015.table
  base := (5139059708280122905127406693558876482741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-90854453014295106767782647838167611500000000000)
      constant := (393437569881638132479874627751124037154351025949) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93463691411723151997/50000000000000000000)
  centralHi := (37385476564689260799/20000000000000000000)
  directionLo := (48372055869173943751/25000000000000000000)
  directionHi := (38697644695339155001/20000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree016.table
  base := (222227580304607290692277443336450243191/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-96789071499309009742723890345110854000000000000)
      constant := (429708405982980543347564007776469746228921695984) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree016.table
  base := (353431296280085454526196449137181189473/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-96895895700281269718872594197274354000000000000)
      constant := (430442037575735816647279820063182371498155490970) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48372055869173943751/25000000000000000000)
  centralHi := (38697644695339155001/20000000000000000000)
  directionLo := (99916888961666890711/50000000000000000000)
  directionHi := (199833777923333781423/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree017.table
  base := (2145062782988599582453637713469188376757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-102823837672734406445304542713457377750000000000)
      constant := (471175369106025414177065474481127587034673205373) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree017.table
  base := (1062844973849323570310067129123488237281/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-102937338386267432669962540556381096500000000000)
      constant := (472038159695293048632562007206442594034872920018) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99916888961666890711/50000000000000000000)
  centralHi := (199833777923333781423/100000000000000000000)
  directionLo := (1287399646787699647/625000000000000000)
  directionHi := (205983943486031943521/100000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree018.table
  base := (36159137901444026594335863032204301263/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-108858603846159803147885195081803901500000000000)
      constant := (517030460023312501991786727303862910421406960175) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree018.table
  base := (886414937952901750521743553537233762449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-108978781072253595621052486915487839000000000000)
      constant := (518028275455168240222314435688700325823203375961) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1287399646787699647/625000000000000000)
  centralHi := (205983943486031943521/100000000000000000000)
  directionLo := (2119557292195738673/1000000000000000000)
  directionHi := (211955729219573867301/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree019.table
  base := (-47459253521315787401760069297533970593/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 204490000000000000000000000000000000000000000
      center := (2494778)
      previous := (1247389)
      next := (1247389)
      square := (16079853409508606936068053536190000000000000)
      linear := (-318264182879737395707661627285735250000000000)
      constant := (1570940746944062652077992434530559091028874972) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree019.table
  base := (-51432600979337931957388808075482734761/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 204490000000000000000000000000000000000000000
      center := (2494778)
      previous := (1247389)
      next := (1247389)
      square := (16079853409508606936068053536190000000000000)
      linear := (-318615578277672461418677100483641500000000000)
      constant := (1574095199752478765405416394962218032977489244) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2119557292195738673/1000000000000000000)
  centralHi := (211955729219573867301/100000000000000000000)
  directionLo := (217763810868440298361/100000000000000000000)
  directionHi := (108881905434220149181/50000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree020.table
  base := (-1155020782074702541242726486712443877759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-120928136193010596553046499818496949000000000000)
      constant := (621275236653568149430445556482052136261877941449) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree020.table
  base := (-584688818281752891504728817562088977961/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-121061666444225921523232379633701324000000000000)
      constant := (622560894837549531575087388201849334777545718942) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217763810868440298361/100000000000000000000)
  centralHi := (108881905434220149181/50000000000000000000)
  directionLo := (223420955818585546461/100000000000000000000)
  directionHi := (111710477909292773231/50000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree021.table
  base := (-501825856376203819083562375100758945379/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-126962902366435993255627152186843472750000000000)
      constant := (679411216582682533910736184197653502482851833076) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree021.table
  base := (-404050329842101271794302510122606139689/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-127103109130212084474322325992808066500000000000)
      constant := (680849776104108640035056534736378714793096848395) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223420955818585546461/100000000000000000000)
  centralHi := (111710477909292773231/50000000000000000000)
  directionLo := (4578767068713361509/2000000000000000000)
  directionHi := (228938353435668075451/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree022.table
  base := (-86250496039327815576090486186071107827/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (7443098)
      previous := (3721549)
      next := (3721549)
      square := (47973777527542207470417911789790000000000000)
      linear := (-1099154285453399917009981855828016500000000000)
      constant := (6127430903559368723628253030978938577792641824) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree022.table
  base := (-554335432410118250298196866832997866257/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (7443098)
      previous := (3721549)
      next := (3721549)
      square := (47973777527542207470417911789790000000000000)
      linear := (-1100368196828084689466217126875329000000000000)
      constant := (6140633443305479034493272171197390540887633435) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4578767068713361509/2000000000000000000)
  centralHi := (228938353435668075451/100000000000000000000)
  directionLo := (58581468832291256309/25000000000000000000)
  directionHi := (234325875329165025237/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree023.table
  base := (-3424484447475663445244019440296648353829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-139032434713286786660788456923536520250000000000)
      constant := (807215392979491713137853261899041986005018331219) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree023.table
  base := (-1717486859964395053165809751047810622607/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-139185994502184410376502218711021551500000000000)
      constant := (808977944557627000938309132380484486176289427954) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58581468832291256309/25000000000000000000)
  centralHi := (234325875329165025237/100000000000000000000)
  directionLo := (119796141448424694203/50000000000000000000)
  directionHi := (239592282896849388407/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree024.table
  base := (-2005174359192117445558642490121496809737/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-145067200886712183363369109291883044000000000000)
      constant := (876728817363762721706284491581519257974610798814) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree024.table
  base := (-4019773685274402839003646772759821589267/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-145227437188170573327592165070128294000000000000)
      constant := (878662562900367405144937144923927637403909561237) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119796141448424694203/50000000000000000000)
  centralHi := (239592282896849388407/100000000000000000000)
  directionLo := (244745394642408799093/100000000000000000000)
  directionHi := (122372697321204399547/50000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree025.table
  base := (-1131455663695010885491185997564639290319/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-151101967060137580065949761660229567750000000000)
      constant := (949898776234802534154803877321653629078560714436) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree025.table
  base := (-566785447436611360735659701604184451789/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-151268879874156736278682111429235036500000000000)
      constant := (952009920396788654384158175637391790054569142232) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244745394642408799093/100000000000000000000)
  centralHi := (122372697321204399547/50000000000000000000)
  directionLo := (124896111202083613389/50000000000000000000)
  directionHi := (249792222404167226779/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree026.table
  base := (-995582401070287616095842991509638543237/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34348089235695900023198623234110000000000000)
      linear := (-929803155228183294488345645139503500000000000)
      constant := (6074991435102261107957043037787298862714323015) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree026.table
  base := (-4985501650226904055794661551166332956767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34348089235695900023198623234110000000000000)
      linear := (-930830311006762717335929336025691000000000000)
      constant := (6088570150058867855452329348423668785115460673) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124896111202083613389/50000000000000000000)
  centralHi := (249792222404167226779/100000000000000000000)
  directionLo := (254739083276511500391/100000000000000000000)
  directionHi := (31842385409563937549/12500000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree027.table
  base := (-5372596699651479096660959700218566870069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-163171499406988373471111066396922615250000000000)
      constant := (1107009001884027077478319237010153669904886705859) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree027.table
  base := (-107588008598169208381408238792995338199/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-163351765246129062180862004147448521500000000000)
      constant := (1109493778023878900861945693762301905310244114450) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254739083276511500391/100000000000000000000)
  centralHi := (31842385409563937549/12500000000000000000)
  directionLo := (129795846161868734619/50000000000000000000)
  directionHi := (259591692323737469239/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree028.table
  base := (-2857492322877083658748087249611358775359/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-169206265580413770173691718765269139000000000000)
      constant := (1190867417258031292902863965476489784593737710098) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree028.table
  base := (-5721080656165914110933802597605407005921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-169393207932115225131951950506555264000000000000)
      constant := (1193548534289441195105942799245895243101067651031) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129795846161868734619/50000000000000000000)
  centralHi := (259591692323737469239/100000000000000000000)
  directionLo := (33044404995978161963/12500000000000000000)
  directionHi := (52871047993565059141/20000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree029.table
  base := (-6009441799875249857361274819279643160297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-175241031753839166876272371133615662750000000000)
      constant := (1278216568776940025118554580323529845669633779567) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree029.table
  base := (-6014901430668636252103034663009712414373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-175434650618101388083041896865662006500000000000)
      constant := (1281100444880152204116263471613936536561443634803) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33044404995978161963/12500000000000000000)
  centralHi := (52871047993565059141/20000000000000000000)
  directionLo := (53806891407473453627/20000000000000000000)
  directionHi := (33629307129670908517/12500000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree030.table
  base := (-1251940475510545276261169149102551794267/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-181275797927264563578853023501962186500000000000)
      constant := (1369028890129306577716024855039820225606806581185) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree030.table
  base := (-3132295245217872150014068336124067770381/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-181476093304087551034131843224768749000000000000)
      constant := (1372121991309568208120557887158288637729031788182) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (53806891407473453627/20000000000000000000)
  centralHi := (33629307129670908517/12500000000000000000)
  directionLo := (13681683490010972707/5000000000000000000)
  directionHi := (273633669800219454141/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree031.table
  base := (-32344811777176677032202248375137622703/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-187310564100689960281433675870308710250000000000)
      constant := (1463280788331068041224236595169875079571294186600) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree031.table
  base := (-3236668872970540698293117715831591440863/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-187517535990073713985221789583875491500000000000)
      constant := (1466589625374669264873449468730245399162572194386) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13681683490010972707/5000000000000000000)
  centralHi := (273633669800219454141/100000000000000000000)
  directionLo := (278156846802806653223/100000000000000000000)
  directionHi := (34769605850350831653/12500000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree032.table
  base := (-6639958867262513120116844746816578482689/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-193345330274115356984014328238655234000000000000)
      constant := (1560952057617354994898338447825176378965304842679) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree032.table
  base := (-166096867367209046441988753940771587487/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-193558978676059876936311735942982234000000000000)
      constant := (1564483182917779677464373918777008864499987186280) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (278156846802806653223/100000000000000000000)
  centralHi := (34769605850350831653/12500000000000000000)
  directionLo := (282607638959431823067/100000000000000000000)
  directionHi := (70651909739857955767/25000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree033.table
  base := (-677503766773112258937673467394865112939/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (7443098)
      previous := (3721549)
      next := (3721549)
      square := (47973777527542207470417911789790000000000000)
      linear := (-1647769392128435980880950252950427750000000000)
      constant := (13735746953869611797988558590778680110434545490) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree033.table
  base := (-6778541888425885901476301451967357989773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (7443098)
      previous := (3721549)
      next := (3721549)
      square := (47973777527542207470417911789790000000000000)
      linear := (-1649590259190463139565303159521396500000000000)
      constant := (13766821370062680893256975337556515925151939043) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282607638959431823067/100000000000000000000)
  centralHi := (70651909739857955767/25000000000000000000)
  directionLo := (286989414043739748069/100000000000000000000)
  directionHi := (28698941404373974807/10000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree034.table
  base := (-1719052622452268456947146225397771466161/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-205414862620966150389175632975348281500000000000)
      constant := (1766485908941858793334914400637356874009306038684) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree034.table
  base := (-3439673141650459014740576272853351091461/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-205641864048032202838491628661195719000000000000)
      constant := (1770481418425185193075961702045713271964175515942) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286989414043739748069/100000000000000000000)
  centralHi := (28698941404373974807/10000000000000000000)
  directionLo := (291305286509039521539/100000000000000000000)
  directionHi := (14565264325451976077/5000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree035.table
  base := (-6945203834183901881903675786811532070077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-211449628794391547091756285343694805250000000000)
      constant := (1874320895006528347328974186624760954149524849147) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree035.table
  base := (-868501251833794987179096211865649841103/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-211683306734018365789581575020302461500000000000)
      constant := (1878558567904107397653066782337481342609884366664) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291305286509039521539/100000000000000000000)
  centralHi := (14565264325451976077/5000000000000000000)
  directionLo := (295558143388163339591/100000000000000000000)
  directionHi := (36944767923520417449/12500000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree036.table
  base := (-3491750245295275561741517743477183875641/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-217484394967816943794336937712041329000000000000)
      constant := (1985519393526440043776405950857410331696306411902) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree036.table
  base := (-6986011898709217603804576412371625797307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-217724749420004528740671521379409204000000000000)
      constant := (1990005917461732467220935680213838523789583765677) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295558143388163339591/100000000000000000000)
  centralHi := (36944767923520417449/12500000000000000000)
  directionLo := (149875333442500336067/50000000000000000000)
  directionHi := (59950133377000134427/20000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree037.table
  base := (-279694995617464002636857081504995021847/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-223519161141242340496917590080387852750000000000)
      constant := (2100071996535518742816841860472556641346400040425) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree037.table
  base := (-874327845262228054617548361656729107477/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-223766192105990691691761467738515946500000000000)
      constant := (2104814085742402606895351696686297097206463764376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (149875333442500336067/50000000000000000000)
  centralHi := (59950133377000134427/20000000000000000000)
  directionLo := (75971338539999394089/25000000000000000000)
  directionHi := (303885354159997576357/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree038.table
  base := (-1743230805382736697400602563270580716841/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 204490000000000000000000000000000000000000000
      center := (2494778)
      previous := (1247389)
      next := (1247389)
      square := (16079853409508606936068053536190000000000000)
      linear := (-635883455165284590580327541409236500000000000)
      constant := (6143962913788915356866928871979264548435273564) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree038.table
  base := (-139498710640333813106523868211868053817/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 204490000000000000000000000000000000000000000
      center := (2494778)
      previous := (1247389)
      next := (1247389)
      square := (16079853409508606936068053536190000000000000)
      linear := (-636586245961154722002358487805049000000000000)
      constant := (6157825497674240362556116984881161883374808350) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75971338539999394089/25000000000000000000)
  centralHi := (303885354159997576357/100000000000000000000)
  directionLo := (307964534724197867373/100000000000000000000)
  directionHi := (153982267362098933687/50000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree039.table
  base := (-108220142085371155183384365180813590187/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34348089235695900023198623234110000000000000)
      linear := (-1394015937799367656225318904243082250000000000)
      constant := (13841469075404161613611839477762659537478165792) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree039.table
  base := (-3463945438032239149117059163454251867281/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34348089235695900023198623234110000000000000)
      linear := (-1395556671467236790496694440572363500000000000)
      constant := (13872672959312391832711993978001456617120597278) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (307964534724197867373/100000000000000000000)
  centralHi := (153982267362098933687/50000000000000000000)
  directionLo := (62398077157180474053/20000000000000000000)
  directionHi := (155995192892951185133/50000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree040.table
  base := (-685268542198541260543262346232519795173/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-241623459661518530604659547185427424000000000000)
      constant := (2463778981115614460449383540887630514277711436030) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree040.table
  base := (-1370859812246363523673953569451804808461/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-241890520163949180545031306815836174000000000000)
      constant := (2469328280669544358740492673102032938466564724855) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62398077157180474053/20000000000000000000)
  centralHi := (155995192892951185133/50000000000000000000)
  directionLo := (78991236459250935969/25000000000000000000)
  directionHi := (315964945837003743877/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree041.table
  base := (-6753413099075049711650327902380829431329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-247658225834943927307240199553773947750000000000)
      constant := (2591677559947762586150729566222196304048797433719) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree041.table
  base := (-1688714649795982980607166405849536583761/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-247931962849935343496121253174942916500000000000)
      constant := (2597509499822370971264354652502612749538431373084) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78991236459250935969/25000000000000000000)
  centralHi := (315964945837003743877/100000000000000000000)
  directionLo := (319890126719667962989/100000000000000000000)
  directionHi := (31989012671966796299/10000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree042.table
  base := (-6628876929360287339880098239828433676207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-253692992008369324009820851922120471500000000000)
      constant := (2722899545518158971681454956985276587590392743577) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree042.table
  base := (-3315086079451467110445563643242371578247/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-253973405535921506447211199534049659000000000000)
      constant := (2729020938626210559648489297746679631251620364034) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (319890126719667962989/100000000000000000000)
  centralHi := (31989012671966796299/10000000000000000000)
  directionLo := (16188386218804342649/5000000000000000000)
  directionHi := (323767724376086852981/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree043.table
  base := (-6479599240714179386173895001008945826313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-259727758181794720712401504290466995250000000000)
      constant := (2857441081955957552479107391946935737356166392143) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree043.table
  base := (-6480760154771340317514388385882822044243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-260014848221907669398301145893156401500000000000)
      constant := (2863858755335774512185654161614864586566986236373) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (16188386218804342649/5000000000000000000)
  centralHi := (323767724376086852981/100000000000000000000)
  directionLo := (163799714226409948513/50000000000000000000)
  directionHi := (327599428452819897027/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree044.table
  base := (-3153015757583818366396754648800470829113/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (7443098)
      previous := (3721549)
      next := (3721549)
      square := (47973777527542207470417911789790000000000000)
      linear := (-2196384498803472044751918650072839000000000000)
      constant := (24754535837856398707931915767118624525373289966) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree044.table
  base := (-6307072356389002486483218288437457928203/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (7443098)
      previous := (3721549)
      next := (3721549)
      square := (47973777527542207470417911789790000000000000)
      linear := (-2198812321552841589664389192167464000000000000)
      constant := (24810079584395431611578222100798707629258263173) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163799714226409948513/50000000000000000000)
  centralHi := (327599428452819897027/100000000000000000000)
  directionLo := (82846707726363054179/25000000000000000000)
  directionHi := (331386830905452216717/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree045.table
  base := (-1527141083503579571555520414029155210851/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-271797290528645514117562809027160042750000000000)
      constant := (3136469925486287520040116984242310160671924109044) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree045.table
  base := (-6109497814077866312716780801233063221121/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-272097733593879995300481038611369886500000000000)
      constant := (3143500689750326617133391110462540778027808098231) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82846707726363054179/25000000000000000000)
  centralHi := (331386830905452216717/100000000000000000000)
  directionLo := (335131433727878319691/100000000000000000000)
  directionHi := (83782858431969579923/25000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree046.table
  base := (-2943767943348736248754901079599808816323/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-277832056702070910820143461395506566500000000000)
      constant := (3280951852728378461105408274552812853338587922506) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree046.table
  base := (-736046668710614090943445749668995296979/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-278139176279866158251570984970476629000000000000)
      constant := (3288299449002361130966533540101445827791956726952) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (335131433727878319691/100000000000000000000)
  centralHi := (83782858431969579923/25000000000000000000)
  directionLo := (67766931182531149327/20000000000000000000)
  directionHi := (84708663978163936659/25000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree047.table
  base := (-2821619627764056374768557322529084759431/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-283866822875496307522724113763853090250000000000)
      constant := (3428742454547192840383021165979706835864361037282) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree047.table
  base := (-88187356636134364313847361244148740229/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-284180618965852321202660931329583371500000000000)
      constant := (3436413752920363950888380216498283031523815063616) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67766931182531149327/20000000000000000000)
  centralHi := (84708663978163936659/25000000000000000000)
  directionLo := (42812229966738245267/12500000000000000000)
  directionHi := (342497839733905962137/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree048.table
  base := (-268796432822744277290968794985966499543/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-289901589048921704225304766132199614000000000000)
      constant := (3579839854297972529954466481861786442987102293460) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree048.table
  base := (-168018855185883557503714671880700307677/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-290222061651838484153750877688690114000000000000)
      constant := (3587841732899862591647475399712971946284832087904) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42812229966738245267/12500000000000000000)
  centralHi := (342497839733905962137/100000000000000000000)
  directionLo := (43265282053956244873/12500000000000000000)
  directionHi := (69224451286329991797/20000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree049.table
  base := (-5085824789112001549426260527594285659293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-295936355222347100927885418500546137750000000000)
      constant := (3734242422756375519260214871068248502551362896923) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree049.table
  base := (-1017286140350116395699531528350465289209/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-296263504337824647104840824047796856500000000000)
      constant := (3742581766886557706923066904958653237936992111995) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43265282053956244873/12500000000000000000)
  centralHi := (69224451286329991797/20000000000000000000)
  directionLo := (349709111365834117489/100000000000000000000)
  directionHi := (34970911136583411749/10000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree050.table
  base := (-4773119426471861392738811104277106550571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-301971121395772497630466070868892661500000000000)
      constant := (3891948744237251752288373195393268361749951877181) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree050.table
  base := (-1193415934809709323214844314900898709167/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-302304947023810810055930770406903599000000000000)
      constant := (3900632445587103790384245023939643467570776360548) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349709111365834117489/100000000000000000000)
  centralHi := (34970911136583411749/10000000000000000000)
  directionLo := (176629774349644889417/50000000000000000000)
  directionHi := (70651909739857955767/20000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree051.table
  base := (-4437979354996961111831160098155812573523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-308005887569197894333046723237239185250000000000)
      constant := (4052957587508091088138494998357415971082121670453) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree051.table
  base := (-221923424659617789126136117712136812463/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-308346389709796973007020716766010341500000000000)
      constant := (4061992543465624615964915218180437450373186495860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (176629774349644889417/50000000000000000000)
  centralHi := (70651909739857955767/20000000000000000000)
  directionLo := (178387327830601804641/50000000000000000000)
  directionHi := (356774655661203609283/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree052.table
  base := (-2040274879845627001909761781893233944253/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34348089235695900023198623234110000000000000)
      linear := (-1858228720370552017962292163346661000000000000)
      constant := (24954247815386230048635650471613784671162169414) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree052.table
  base := (-4080989460969449993774682184795108040007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34348089235695900023198623234110000000000000)
      linear := (-1860283031927710863657459545119036000000000000)
      constant := (25009828365856573109814025523243359385704454233) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (178387327830601804641/50000000000000000000)
  centralHi := (356774655661203609283/100000000000000000000)
  directionLo := (360255466436131850609/100000000000000000000)
  directionHi := (36025546643613185061/10000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree053.table
  base := (-3700957134445887827976895585587172910911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-320075419916048687738208027973932232750000000000)
      constant := (4384878690324634713460059171801561346305453426921) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree053.table
  base := (-462669065468819969254561548846534259409/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-320429275081769298909200609484223826500000000000)
      constant := (4394636867413435077300042107701868044012699396792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360255466436131850609/100000000000000000000)
  centralHi := (36025546643613185061/10000000000000000000)
  directionLo := (45462870714748411621/12500000000000000000)
  directionHi := (363702965717987292969/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree054.table
  base := (-3299311786178587940239446875621266445239/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-326110186089474084440788680342278756500000000000)
      constant := (4555789201785692629605320234138266241027282075729) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree054.table
  base := (-3299667442516486531991854444258743134759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-326470717767755461860290555843330569000000000000)
      constant := (4565919353951318277456176803885299514526070068449) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45462870714748411621/12500000000000000000)
  centralHi := (363702965717987292969/100000000000000000000)
  directionLo := (367118091963613198639/100000000000000000000)
  directionHi := (4588976149545164983/1250000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree055.table
  base := (-2875709991158671993155144789304937508601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (7443098)
      previous := (3721549)
      next := (3721549)
      square := (47973777527542207470417911789790000000000000)
      linear := (-2744999605478508108622887047195250250000000000)
      constant := (39090898383995520130370478883686507059725261591) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree055.table
  base := (-575206001413799931305475164285294872293/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (7443098)
      previous := (3721549)
      next := (3721549)
      square := (47973777527542207470417911789790000000000000)
      linear := (-2748034383915220039763475224813531500000000000)
      constant := (39177749969541888450278208220506242694431381815) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (367118091963613198639/100000000000000000000)
  centralHi := (4588976149545164983/1250000000000000000)
  directionLo := (370501740376409670057/100000000000000000000)
  directionHi := (185250870188204835029/50000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree056.table
  base := (-2430235853318808363617865154674864441277/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-338179718436324877845949985078971804000000000000)
      constant := (4907506577495214424002866169247449231131557912347) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree056.table
  base := (-1215261943907372306052952029570948259857/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-338553603139727787762470448561544054000000000000)
      constant := (4918401426840797229224748422379156840262680997454) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370501740376409670057/100000000000000000000)
  centralHi := (185250870188204835029/50000000000000000000)
  directionLo := (93463691411723151997/25000000000000000000)
  directionHi := (373854765646892607989/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree057.table
  base := (-392592581409981203510031520545468597991/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 204490000000000000000000000000000000000000000
      center := (2494778)
      previous := (1247389)
      next := (1247389)
      square := (16079853409508606936068053536190000000000000)
      linear := (-953502727450831785452993455532737750000000000)
      constant := (14095047861616464940476722101439002930385910205) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree057.table
  base := (-78528889309350616763537362001859759333/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 204490000000000000000000000000000000000000000
      center := (2494778)
      previous := (1247389)
      next := (1247389)
      square := (16079853409508606936068053536190000000000000)
      linear := (-954556913644636982586039875126456500000000000)
      constant := (14126315389321622167582298644191077713284987075) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93463691411723151997/25000000000000000000)
  centralHi := (373854765646892607989/100000000000000000000)
  directionLo := (377177984473958276963/100000000000000000000)
  directionHi := (94294496118489569241/25000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree058.table
  base := (-5895822003047792468730643134137642469/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-350249250783175671251111289815664851500000000000)
      constant := (5272415331082756690110431460000488197479665564750) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree058.table
  base := (-1474189045745771075149501973177562199697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-350636488511700113664650341279757539000000000000)
      constant := (5284102559944861981626113140095348759413800972967) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (377177984473958276963/100000000000000000000)
  centralHi := (94294496118489569241/25000000000000000000)
  directionLo := (1521888711551706221/400000000000000000)
  directionHi := (380472177887926555251/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree059.table
  base := (-481634996102992874140356193646586500521/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-356284016956601067953691942184011375250000000000)
      constant := (5459815320574918864839204157446384188306098363262) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree059.table
  base := (-963480377405151370572814438413476321913/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-356677931197686276615740287638864281500000000000)
      constant := (5471909126269885361838892753562255510460995583743) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1521888711551706221/400000000000000000)
  centralHi := (380472177887926555251/100000000000000000000)
  directionLo := (383738093394083755133/100000000000000000000)
  directionHi := (191869046697041877567/50000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree060.table
  base := (-215477891025480344770772165332902099977/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-362318783130026464656272594552357899000000000000)
      constant := (5650511881839895579952253500894727278514365776094) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree060.table
  base := (-43114535435959796000742898289537814341/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-362719373883672439566830233997971024000000000000)
      constant := (5663019191862890211696372044448402593356692616510) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (383738093394083755133/100000000000000000000)
  centralHi := (191869046697041877567/50000000000000000000)
  directionLo := (386976446953391550009/100000000000000000000)
  directionHi := (38697644695339155001/10000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree061.table
  base := (61471895812523597688642045722715936081/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-368353549303451861358853246920704422750000000000)
      constant := (5844504694952137360946951522107771709590924006418) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree061.table
  base := (122772929821668061329130556132240366213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-368760816569658602517920180357077766500000000000)
      constant := (5857432438603313213412977777427629653621526958957) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386976446953391550009/100000000000000000000)
  centralHi := (38697644695339155001/10000000000000000000)
  directionLo := (39018792481523000353/10000000000000000000)
  directionHi := (390187924815230003531/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree062.table
  base := (698390678536651445120503675641152532619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-374388315476877258061433899289050946500000000000)
      constant := (6041793479021051009566178563207064136027118861091) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree062.table
  base := (349118321553095964153213420342508855633/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-374802259255644765469010126716184509000000000000)
      constant := (6055148587211723735024042967462013054086141914674) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39018792481523000353/10000000000000000000)
  centralHi := (390187924815230003531/100000000000000000000)
  directionLo := (49171648151933056373/12500000000000000000)
  directionHi := (78674637043092890197/20000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree063.table
  base := (1295351444478898355220885121597635856019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-380423081650302654764014551657397470250000000000)
      constant := (6242377987232359913322677839914207113758410943691) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree063.table
  base := (1295212546179887374958424665227057055617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-380843701941630928420100073075291251500000000000)
      constant := (6256167392312546892760528671687153511611392643913) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49171648151933056373/12500000000000000000)
  centralHi := (78674637043092890197/20000000000000000000)
  directionLo := (99133214987934485889/25000000000000000000)
  directionHi := (396532859951737943557/100000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree064.table
  base := (15310373507756348535057774473074263991/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-386457847823728051466595204025743994000000000000)
      constant := (6446258002545396456940067822096638266048882149875) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree064.table
  base := (1913671412160177092907399315842335250739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-386885144627617091371190019434397994000000000000)
      constant := (6460488638150334308382610080647423404788792613771) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99133214987934485889/25000000000000000000)
  centralHi := (396532859951737943557/100000000000000000000)
  directionLo := (79933511169333512569/20000000000000000000)
  directionHi := (199833777923333781423/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree065.table
  base := (1276850268271025944455001091924881456163/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34348089235695900023198623234110000000000000)
      linear := (-2322441502941736379699265422450239750000000000)
      constant := (39369428011575366240327329048214429735960812006) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree065.table
  base := (1276793761336219726785315117157913789431/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34348089235695900023198623234110000000000000)
      linear := (-2325009392388184936818224649665708500000000000)
      constant := (39456284821714530116489731404260057633222271022) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79933511169333512569/20000000000000000000)
  centralHi := (199833777923333781423/50000000000000000000)
  directionLo := (100694464027135589637/25000000000000000000)
  directionHi := (402777856108542358549/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree066.table
  base := (3215040201716812573239066332909569169417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (7443098)
      previous := (3721549)
      next := (3721549)
      square := (47973777527542207470417911789790000000000000)
      linear := (-3293614712153544172493855444317661500000000000)
      constant := (56726477795449336352238484403249848124206961753) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree066.table
  base := (1607469114924572788852073492665362100287/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (7443098)
      previous := (3721549)
      next := (3721549)
      square := (47973777527542207470417911789790000000000000)
      linear := (-3297256446277598489862561257459599000000000000)
      constant := (56851551365968900646911925696180620527752819166) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (100694464027135589637/25000000000000000000)
  centralHi := (402777856108542358549/100000000000000000000)
  directionLo := (405864321598164342357/100000000000000000000)
  directionHi := (202932160799082171179/50000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree067.table
  base := (3897795601157243884732278374261817541343/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-404562146344004241574337161130783565250000000000)
      constant := (7077669292171507850132125068745216747009142705527) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree067.table
  base := (3897703575286884540436536130896059543057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-405009472685575580224459858511718221500000000000)
      constant := (7093265232053068196800372198846094147264896106073) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405864321598164342357/100000000000000000000)
  centralHi := (202932160799082171179/50000000000000000000)
  directionLo := (408927492009625941717/100000000000000000000)
  directionHi := (204463746004812970859/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree068.table
  base := (2300974511390988994789601184542612801331/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-410596912517429638276917813499130089000000000000)
      constant := (7294729639970490316558198129775016735358929520918) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree068.table
  base := (575233244782241555649120921024681744133/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-411050915371561743175549804870824964000000000000)
      constant := (7310794555252110722686909983689394229154920270696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408927492009625941717/100000000000000000000)
  centralHi := (204463746004812970859/50000000000000000000)
  directionLo := (1287399646787699647/312500000000000000)
  directionHi := (411967886972063887041/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree069.table
  base := (2663742417342990755447800094171755424013/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-416631678690855034979498465867476612750000000000)
      constant := (7515084741250202901962945807316892266394780906314) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree069.table
  base := (5327409846551917903946027741724108507779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-417092358057547906126639751229931706500000000000)
      constant := (7531625570219205227626484466890421571418831770331) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1287399646787699647/312500000000000000)
  centralHi := (411967886972063887041/100000000000000000000)
  directionLo := (414986007078758890391/100000000000000000000)
  directionHi := (51873250884844861299/12500000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree070.table
  base := (1518597307912325584612026805774179838299/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-422666444864280431682079118235823136500000000000)
      constant := (7738734494099283255292887593058198404592065306444) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree070.table
  base := (6074321524246476893217868240079162476633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-423133800743534069077729697589038449000000000000)
      constant := (7755758175702192103307384077518482533822965226337) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (414986007078758890391/100000000000000000000)
  centralHi := (51873250884844861299/12500000000000000000)
  directionLo := (417982334849352505051/100000000000000000000)
  directionHi := (104495583712338126263/25000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree071.table
  base := (1710662503451276009855570630218546605669/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-428701211037705828384659770604169660250000000000)
      constant := (7965678808457228601852544763402551933279473350164) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree071.table
  base := (6842588871496518615933147365078251614971/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-429175243429520232028819643948145191500000000000)
      constant := (7983192282231296223252517704928586801104859654419) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (417982334849352505051/100000000000000000000)
  centralHi := (104495583712338126263/25000000000000000000)
  directionLo := (420957335630418441291/100000000000000000000)
  directionHi := (105239333907604610323/25000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree072.table
  base := (7632256393218277822871263596268305498221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-434735977211131225087240422972516184000000000000)
      constant := (8195917604686541842322465185211912699567056763669) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree072.table
  base := (1908050293027335742510864507015109840873/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-435216686115506394979909590307251934000000000000)
      constant := (8213927810698629334158254925684008448760401294788) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (420957335630418441291/100000000000000000000)
  centralHi := (105239333907604610323/25000000000000000000)
  directionLo := (2119557292195738673/500000000000000000)
  directionHi := (423911458439147734601/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree073.table
  base := (8443198824708810862002237470556763911557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-440770743384556621789821075340862707750000000000)
      constant := (8429450812323854600994122728516997485051789402573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree073.table
  base := (8443148945253941979538414435601070557333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-441258128801492557930999536666358676500000000000)
      constant := (8447964691115853141185977206933351057568261808637) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2119557292195738673/500000000000000000)
  centralHi := (423911458439147734601/100000000000000000000)
  directionLo := (426845136754478901061/100000000000000000000)
  directionHi := (213422568377239450531/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree074.table
  base := (4637734428877181877333595910469688662389/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-446805509557982018492401727709209231500000000000)
      constant := (8666278368986658871912653975177798599734843101242) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree074.table
  base := (4637711899075743868168619351343686236063/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-447299571487478720882089483025465419000000000000)
      constant := (8685302861526727379402548427140218573140384151214) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (426845136754478901061/100000000000000000000)
  centralHi := (213422568377239450531/50000000000000000000)
  directionLo := (42975878925961981141/10000000000000000000)
  directionHi := (429758789259619811411/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree075.table
  base := (1012905900673619111957600940048572973047/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-452840275731407415194982380077555755250000000000)
      constant := (8906400219415450856605036344857040735842463051830) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree075.table
  base := (5064509148511130941866142422974999350649/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-453341014173464883833179429384572161500000000000)
      constant := (8925942267054428561503818996674885960431616251522) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (42975878925961981141/10000000000000000000)
  centralHi := (429758789259619811411/100000000000000000000)
  directionLo := (43265282053956244873/10000000000000000000)
  directionHi := (432652820539562448731/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree076.table
  base := (5501981318580932330256481108249049501071/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 204490000000000000000000000000000000000000000
      center := (2494778)
      previous := (1247389)
      next := (1247389)
      square := (16079853409508606936068053536190000000000000)
      linear := (-1271121999736378980325659369656239000000000000)
      constant := (25345751564082595511253426510561878001494801758) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree076.table
  base := (11003925853932336174888871277570908118909/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 204490000000000000000000000000000000000000000
      center := (2494778)
      previous := (1247389)
      next := (1247389)
      square := (16079853409508606936068053536190000000000000)
      linear := (-1272527581328119243169721262447864000000000000)
      constant := (25401337559740282833939172653100884000123570141) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43265282053956244873/10000000000000000000)
  centralHi := (432652820539562448731/100000000000000000000)
  directionLo := (435527621736880596723/100000000000000000000)
  directionHi := (108881905434220149181/25000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree077.table
  base := (11900173865815948207967462754115364314491/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (7443098)
      previous := (3721549)
      next := (3721549)
      square := (47973777527542207470417911789790000000000000)
      linear := (-3842229818828580236364823841440072750000000000)
      constant := (77657244720754853593453385190646253316150281419) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree077.table
  base := (11900140627499874949899715643526848679309/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (7443098)
      previous := (3721549)
      next := (3721549)
      square := (47973777527542207470417911789790000000000000)
      linear := (-3846478508639976939961647290105666500000000000)
      constant := (77827475987112127357209968019324701729825962781) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (435527621736880596723/100000000000000000000)
  centralHi := (108881905434220149181/25000000000000000000)
  directionLo := (438383571168819995259/100000000000000000000)
  directionHi := (21919178558440999763/5000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree078.table
  base := (12817687473063261933058158054341056067903/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34348089235695900023198623234110000000000000)
      linear := (-2786654285512920741436238681553818500000000000)
      constant := (57080065506604735664576019764138411388852070943) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree078.table
  base := (1602207179461677057484676660376522976401/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34348089235695900023198623234110000000000000)
      linear := (-2789735752848659009978989754212381000000000000)
      constant := (57205132751024775334819709657966942576057376648) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438383571168819995259/100000000000000000000)
  centralHi := (21919178558440999763/5000000000000000000)
  directionLo := (55152629363554653581/12500000000000000000)
  directionHi := (441221034908437228649/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree079.table
  base := (13756498825764996120389195663707991264701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-476979340425109002005304989550941850250000000000)
      constant := (9899829658646163064405833313484059475456932840389) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree079.table
  base := (1719558959898653170016376276178084159871/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-477506784917409535637539214820999131500000000000)
      constant := (9921511346561483813011461433519789737160013604152) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55152629363554653581/12500000000000000000)
  centralHi := (441221034908437228649/100000000000000000000)
  directionLo := (444040367332314620563/100000000000000000000)
  directionHi := (111010091833078655141/25000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree080.table
  base := (14716603809471100924283973728627941889687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-483014106598534398707885641919288374000000000000)
      constant := (10156422344927989042070096588001447234916497616143) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree080.table
  base := (2943315854791437694312698127648399133259/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-483548227603395698588629161180105874000000000000)
      constant := (10178656299206783980335030524152669635546203990255) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (444040367332314620563/100000000000000000000)
  centralHi := (111010091833078655141/25000000000000000000)
  directionLo := (223420955818585546461/50000000000000000000)
  directionHi := (446841911637171092923/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree081.table
  base := (15697998768727703228089252154172495780173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-489048872771959795410466294287634897750000000000)
      constant := (10416309102476792433564295563172424815881049021397) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree081.table
  base := (15697976591919354762971210942635529545123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-489589670289381861539719107539212616500000000000)
      constant := (10439102266076293200105251129717521319382977501947) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223420955818585546461/50000000000000000000)
  centralHi := (446841911637171092923/100000000000000000000)
  directionLo := (449626000327501008201/100000000000000000000)
  directionHi := (224813000163750504101/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree082.table
  base := (16700680454489727419285702006381859622449/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-495083638945385192113046946655981421500000000000)
      constant := (10679489907307833325705083038586225901687174915961) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree082.table
  base := (16700660408676030739674198109826634378397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-495631112975368024490809053898319359000000000000)
      constant := (10702849223367205963371674662916414726926786331333) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449626000327501008201/100000000000000000000)
  centralHi := (224813000163750504101/50000000000000000000)
  directionLo := (113098238919050606959/25000000000000000000)
  directionHi := (452392955676202427837/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree083.table
  base := (8862322988879896329674725701111274060679/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-501118405118810588815627599024327945250000000000)
      constant := (10945964738094275932375581163377699713905835056862) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree083.table
  base := (8862313928712347040944711551472996647227/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-501672555661354187441899000257426101500000000000)
      constant := (10969897149916530904945176342709596279661812634406) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113098238919050606959/25000000000000000000)
  centralHi := (452392955676202427837/100000000000000000000)
  directionLo := (455143090160001190157/100000000000000000000)
  directionHi := (227571545080000595079/50000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree084.table
  base := (18769892768687705957518110346493725198949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-507153171292235985518208251392674469000000000000)
      constant := (11215733575865257412250805796749564107735184224461) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree084.table
  base := (2346234548538719281666127997961137782301/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-507713998347340350392988946616532844000000000000)
      constant := (11240246026901007118339321442648789619701668854312) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (455143090160001190157/100000000000000000000)
  centralHi := (227571545080000595079/50000000000000000000)
  directionLo := (457876706871336150901/100000000000000000000)
  directionHi := (228938353435668075451/50000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree085.table
  base := (19836418540462933019629370269928043750193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-513187937465661382220788903761020992750000000000)
      constant := (11488796403739338875033698596398024862052005993177) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree085.table
  base := (19836403732538826623406329505489000886863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-513755441033326513344078892975639586500000000000)
      constant := (11513895837572207297688887033378096501036651596807) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457876706871336150901/100000000000000000000)
  centralHi := (228938353435668075451/50000000000000000000)
  directionLo := (92118819981648485657/20000000000000000000)
  directionHi := (230297049954121214143/50000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree086.table
  base := (5231055314354354469180019408215028080843/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-519222703639086778923369556129367516500000000000)
      constant := (11765153206689037557104392325172607026939878884108) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree086.table
  base := (10462103935342900197388075586585145949987/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-519796883719312676295168839334746329000000000000)
      constant := (11790846567022548164164009969704356070336587165686) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92118819981648485657/20000000000000000000)
  centralHi := (230297049954121214143/50000000000000000000)
  directionLo := (57911944342956537533/12500000000000000000)
  directionHi := (92659110948730460053/20000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree087.table
  base := (881331964273193831831847188120514498579/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-525257469812512175625950208497714040250000000000)
      constant := (12044803971332683380906913649332948110412201288275) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree087.table
  base := (22033287004674372643224217640546379269237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-525838326405298839246258785693853071500000000000)
      constant := (12071098201978470420787180245479869065112012496093) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (57911944342956537533/12500000000000000000)
  centralHi := (92659110948730460053/20000000000000000000)
  directionLo := (232990674287713199857/50000000000000000000)
  directionHi := (93196269715085279943/20000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree088.table
  base := (11581825236993226024729207519321664581031/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (7443098)
      previous := (3721549)
      next := (3721549)
      square := (47973777527542207470417911789790000000000000)
      linear := (-4390844925503616300235792238562484000000000000)
      constant := (101882220543391038228913557705634985368848240558) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree088.table
  base := (23163639532999436060905157885893319770049/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (7443098)
      previous := (3721549)
      next := (3721549)
      square := (47973777527542207470417911789790000000000000)
      linear := (-4395700571002355390060733322751734000000000000)
      constant := (102104551492706783731052338294084697545850919441) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (232990674287713199857/50000000000000000000)
  centralHi := (93196269715085279943/20000000000000000000)
  directionLo := (58581468832291256309/12500000000000000000)
  directionHi := (468651750658330050473/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree089.table
  base := (24315273920109101641143994570091491582691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-537327002159362969031111513234407087750000000000)
      constant := (12613987339320746047680631621318804911060863321499) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree089.table
  base := (3039408003599883985238625085384610270129/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-537921211777271165148438678412066556500000000000)
      constant := (12641504142406477721133750460438732063174000555848) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58581468832291256309/12500000000000000000)
  centralHi := (468651750658330050473/100000000000000000000)
  directionLo := (94261404523816019497/20000000000000000000)
  directionHi := (235653511309540048743/50000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree090.table
  base := (12744084081404871893172585654655911585873/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-543361768332788365733692165602753611500000000000)
      constant := (12903519922577271923425431056688629141624841257394) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree090.table
  base := (25488159220438049682227272983748488402017/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-543962654463257328099528624771173299000000000000)
      constant := (12931658427958016643290894541246309539374157273513) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94261404523816019497/20000000000000000000)
  centralHi := (235653511309540048743/50000000000000000000)
  directionLo := (94789483751101123163/20000000000000000000)
  directionHi := (59243427344438201977/12500000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree091.table
  base := (26682332058772460779732216397330154224669/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34348089235695900023198623234110000000000000)
      linear := (-3250867068084105103173211940657397250000000000)
      constant := (78084890101064102919026739382890474271375266589) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree091.table
  base := (26682323974305649672985740566052045564997/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34348089235695900023198623234110000000000000)
      linear := (-3254462113309133083139754858759053500000000000)
      constant := (78255109934341552503510262539493452121074633957) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (94789483751101123163/20000000000000000000)
  centralHi := (59243427344438201977/12500000000000000000)
  directionLo := (476573186320790727413/100000000000000000000)
  directionHi := (238286593160395363707/50000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree092.table
  base := (13948882294200513631118515976566894859239/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-555431300679639159138853470339446659000000000000)
      constant := (13492466845301680377686197662760040816984089540542) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree092.table
  base := (1394887863978357051696781467072952215771/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-556045539835229654001708517489386784000000000000)
      constant := (13521869587781522963334650491760572335491374512380) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (476573186320790727413/100000000000000000000)
  centralHi := (238286593160395363707/50000000000000000000)
  directionLo := (119796141448424694203/25000000000000000000)
  directionHi := (479184565793698776813/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree093.table
  base := (14567232421100949296458340231217996584671/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-561466066853064555841434122707793182750000000000)
      constant := (13791881170528850585072553369191377676746662215438) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree093.table
  base := (29134458234640094742272607485386598183019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-562086982521215816952798463848493526500000000000)
      constant := (13821926447935856682132618301890243064663034546691) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119796141448424694203/25000000000000000000)
  centralHi := (479184565793698776813/100000000000000000000)
  directionLo := (96356358227122749553/20000000000000000000)
  directionHi := (240890895567806873883/50000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree094.table
  base := (30392432008700481014264026025526605216751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-567500833026489952544014775076139706500000000000)
      constant := (14094589396770966343117823979655745260546670172839) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree094.table
  base := (30392426035194503779381185162597526090737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-568128425207201979903888410207600269000000000000)
      constant := (14125284153429087832305093596821089389156642609593) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (96356358227122749553/20000000000000000000)
  centralHi := (240890895567806873883/50000000000000000000)
  directionLo := (121091272508794132779/25000000000000000000)
  directionHi := (484365090035176531117/100000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree095.table
  base := (7917916340928235055215540826767918611879/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 204490000000000000000000000000000000000000000
      center := (2494778)
      previous := (1247389)
      next := (1247389)
      square := (16079853409508606936068053536190000000000000)
      linear := (-1588741272021926175198325283779740250000000000)
      constant := (39890835231806199818886893952529455662964754684) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree095.table
  base := (6334331992699992806391834604655034380287/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 204490000000000000000000000000000000000000000
      center := (2494778)
      previous := (1247389)
      next := (1247389)
      square := (16079853409508606936068053536190000000000000)
      linear := (-1590498249011601503753402649769271500000000000)
      constant := (39977680606545337098841311719883414458962444315) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (121091272508794132779/25000000000000000000)
  centralHi := (484365090035176531117/100000000000000000000)
  directionLo := (19477387365649600801/4000000000000000000)
  directionHi := (243467342070620010013/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree096.table
  base := (515190066575267865787512325129453674733/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-579570365373340745949176079812832754000000000000)
      constant := (14709887531490120243657113514768491511088387663168) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree096.table
  base := (32972159378964398353605957677574962479599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-580211310579174305806068302925813754000000000000)
      constant := (14741902079808285537072882746362288421196060502311) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19477387365649600801/4000000000000000000)
  centralHi := (243467342070620010013/50000000000000000000)
  directionLo := (244745394642408799093/50000000000000000000)
  directionHi := (489490789284817598187/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree097.table
  base := (8573482030721250999741592490110747601849/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-585605131546766142651756732181179277750000000000)
      constant := (15022477430934801770672502707645102363043231030244) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree097.table
  base := (34293923709727383529832865962161822067633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-586252753265160468757158249284920496500000000000)
      constant := (15055162291743819825731579768490565727624180825337) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244745394642408799093/50000000000000000000)
  centralHi := (489490789284817598187/100000000000000000000)
  directionLo := (98406723138130805363/20000000000000000000)
  directionHi := (7688025245166469169/1562500000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree098.table
  base := (69603430536239950114174025890657764213/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-591639897720191539354337384549525801500000000000)
      constant := (15338361213211637018783478766175698538056977049984) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree098.table
  base := (7127390489037482071720734844763517598391/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-592294195951146631708248195644027239000000000000)
      constant := (15371723331000163774194054213030782925696943093995) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (98406723138130805363/20000000000000000000)
  centralHi := (7688025245166469169/1562500000000000000)
  directionLo := (494563368179005690367/100000000000000000000)
  directionHi := (965944078474620489/195312500000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree099.table
  base := (9250312183884202712521807793860444363031/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (7443098)
      previous := (3721549)
      next := (3721549)
      square := (47973777527542207470417911789790000000000000)
      linear := (-4939460032178652364106760635684895250000000000)
      constant := (129401147726634091726894667113313791955264133116) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree099.table
  base := (740024902587133381788023686673079802197/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (7443098)
      previous := (3721549)
      next := (3721549)
      square := (47973777527542207470417911789790000000000000)
      linear := (-4944922633364733840159819355397801500000000000)
      constant := (129682522266208056098900167994750854001361838650) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494563368179005690367/100000000000000000000)
  centralHi := (965944078474620489/195312500000000000)
  directionLo := (248540123179089162537/50000000000000000000)
  directionHi := (19883209854327133003/4000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree100.table
  base := (3838680461465667194336923494573729693289/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-603709430067042332759498689286218849000000000000)
      constant := (15980010413032741463197462149987064905953021007210) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree100.table
  base := (9596700338737366068384444546580116931731/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-604377081323118957610428088362240724000000000000)
      constant := (16014747878370233614821071181441067737781780664236) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (248540123179089162537/50000000000000000000)
  centralHi := (19883209854327133003/4000000000000000000)
  directionLo := (124896111202083613389/25000000000000000000)
  directionHi := (499584444808334453557/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree101.table
  base := (198968118522774704969169897258511721757/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-609744196240467729462079341654565372750000000000)
      constant := (16305775824829805611550219655594725819752869574600) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree101.table
  base := (39793620758121348331134437733492778249103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-610418524009105120561518034721347466500000000000)
      constant := (16341211380791408160566005254794090276860892516167) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124896111202083613389/25000000000000000000)
  centralHi := (499584444808334453557/100000000000000000000)
  directionLo := (251038076628524767047/50000000000000000000)
  directionHi := (100415230651409906819/20000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree102.table
  base := (1030542641924181602388446236100782628493/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-615778962413893126164659994022911896500000000000)
      constant := (16634835107890640867951353840781820333046320475080) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree102.table
  base := (20610851506892857870990380095934572246249/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-616459966695091283512607981080454209000000000000)
      constant := (16670975699074880170543638055351739518372480068322) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (251038076628524767047/50000000000000000000)
  centralHi := (100415230651409906819/20000000000000000000)
  directionLo := (31534722296691567441/6250000000000000000)
  directionHi := (504555556747065079057/100000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree103.table
  base := (42671050238521114561154791423835111356099/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-621813728587318522867240646391258420250000000000)
      constant := (16967188260049545130240148606600787945160321010811) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree103.table
  base := (2133552391572154398755836088200763092619/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-622501409381077446463697927439560951500000000000)
      constant := (17004040831076156639784833431999237454071324021820) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31534722296691567441/6250000000000000000)
  centralHi := (504555556747065079057/100000000000000000000)
  directionLo := (3961115904661394523/781250000000000000)
  directionHi := (101404567159331699789/20000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree104.table
  base := (44141657126991064828765783122529996590757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34348089235695900023198623234110000000000000)
      linear := (-3715079850655289464910185199760976000000000000)
      constant := (102383640706335780793440619644212789281080856517) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree104.table
  base := (22070827475732894608017493182026159644437/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34348089235695900023198623234110000000000000)
      linear := (-3719188473769607156300519963305726000000000000)
      constant := (102605957247802621056590241056791213358857305194) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3961115904661394523/781250000000000000)
  centralHi := (101404567159331699789/20000000000000000000)
  directionLo := (509478166553023000783/100000000000000000000)
  directionHi := (31842385409563937549/6250000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree105.table
  base := (22816763053980801790512609184706625414663/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-633883260934169316272401951127951467750000000000)
      constant := (17641776164123770171980149672084264065206095842014) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree105.table
  base := (9126704828357458331705984662144632763957/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-634584294753049772365877820157774436500000000000)
      constant := (17680073528769203364694005257157001393897982830865) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (509478166553023000783/100000000000000000000)
  centralHi := (31842385409563937549/6250000000000000000)
  directionLo := (511921720939026343277/100000000000000000000)
  directionHi := (255960860469513171639/50000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree106.table
  base := (2357332848592614357051452784733173032921/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-639918027107594712974982603496297991500000000000)
      constant := (17984010912761473296023810584647783487347205039380) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree106.table
  base := (47146655194951307121212762160550190346613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-640625737439035935316967766516881179000000000000)
      constant := (18023041091216377075210936940662775312480638014557) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (511921720939026343277/100000000000000000000)
  centralHi := (255960860469513171639/50000000000000000000)
  directionLo := (514353666793694472803/100000000000000000000)
  directionHi := (128588416698423618201/25000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree107.table
  base := (48681049531265157492657787718583088060371/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-645952793281020109677563255864644515250000000000)
      constant := (18329539523900467921729189819449435636198683595019) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree107.table
  base := (24340523962740407635765287383390007791247/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-646667180125022098268057712875987921500000000000)
      constant := (18369309460850956218564830476325098276920107549966) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (514353666793694472803/100000000000000000000)
  centralHi := (128588416698423618201/25000000000000000000)
  directionLo := (516774168006744893939/100000000000000000000)
  directionHi := (25838708400337244697/5000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree108.table
  base := (2009468144744755950458215011849408070061/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-651987559454445506380143908232991039000000000000)
      constant := (18678361996303653860573940068933812185637713435725) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree108.table
  base := (25118351083765865840305148047393743543823/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-652708622811008261219147659235094664000000000000)
      constant := (18718878636448665003378230728355579330267353572494) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (516774168006744893939/100000000000000000000)
  centralHi := (25838708400337244697/5000000000000000000)
  directionLo := (129795846161868734619/25000000000000000000)
  directionHi := (519183384647474938477/100000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree109.table
  base := (103627238168076426461560162105148695607/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-658022325627870903082724560601337562750000000000)
      constant := (19030478328864638325912315246683701215719579011500) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree109.table
  base := (51813617772799904472556146104196859979087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-658750065496994424170237605594201406500000000000)
      constant := (19071748616914708981433758093771741130354908372743) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (129795846161868734619/25000000000000000000)
  centralHi := (519183384647474938477/100000000000000000000)
  directionLo := (521581473088291771413/100000000000000000000)
  directionHi := (260790736544145885707/50000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree110.table
  base := (26705897896735220588270703635924216589547/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (7443098)
      previous := (3721549)
      next := (3721549)
      square := (47973777527542207470417911789790000000000000)
      linear := (-5488075138853688427977729032807306500000000000)
      constant := (160213954715651509528713750863695240278573345846) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree110.table
  base := (26705897304326825185480369914904505734979/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (7443098)
      previous := (3721549)
      next := (3721549)
      square := (47973777527542207470417911789790000000000000)
      linear := (-5494144695727112290258905388043869000000000000)
      constant := (160561317365867679855910426913249767355770667622) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (521581473088291771413/100000000000000000000)
  centralHi := (260790736544145885707/50000000000000000000)
  directionLo := (52396858612315390517/10000000000000000000)
  directionHi := (523968586123153905171/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree111.table
  base := (11006246725400916421471092617359702524333/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-670091857974721696487885865338030610250000000000)
      constant := (19744592570606043164053646276855688039670441858185) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree111.table
  base := (55031232556467155325531534420578813342523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-670832950868966750072417498312414891500000000000)
      constant := (19787390988638799529755731389187292609827642270547) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52396858612315390517/10000000000000000000)
  centralHi := (523968586123153905171/100000000000000000000)
  directionLo := (526344873081178087063/100000000000000000000)
  directionHi := (65793109135147260883/12500000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree112.table
  base := (28335966238685323744311994659173182508183/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-676126624148147093190466517706377134000000000000)
      constant := (20106590478109393256758778585224370747377300268574) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree112.table
  base := (28335965755066410233171316848519871459391/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-676874393554952913023507444671521634000000000000)
      constant := (20150163378237844044571374902822371566763568495598) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (526344873081178087063/100000000000000000000)
  centralHi := (65793109135147260883/12500000000000000000)
  directionLo := (33044404995978161963/6250000000000000000)
  directionHi := (528710479935650591409/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree113.table
  base := (729173653107496621099512257953134641247/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-682161390321572489893047170074723657750000000000)
      constant := (20471882242395431913714708005910857126233161498640) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree113.table
  base := (29166945687366536820358878933222903765891/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-682915836240939075974597391030628376500000000000)
      constant := (20516236569366432841717114311789506248595235052598) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33044404995978161963/6250000000000000000)
  centralHi := (528710479935650591409/100000000000000000000)
  directionLo := (531065549408668105079/100000000000000000000)
  directionHi := (13276638735216702627/2500000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree114.table
  base := (60017112854827346363706969476523954971299/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 204490000000000000000000000000000000000000000
      center := (2494778)
      previous := (1247389)
      next := (1247389)
      square := (16079853409508606936068053536190000000000000)
      linear := (-1906360544307473370070991197903241500000000000)
      constant := (57729827874876176964920708979681928573958093251) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree114.table
  base := (30008556032677163850593524385569588616197/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 204490000000000000000000000000000000000000000
      center := (2494778)
      previous := (1247389)
      next := (1247389)
      square := (16079853409508606936068053536190000000000000)
      linear := (-1908468916695083764337084037090679000000000000)
      constant := (57854876901378743112357537391555375410225224906) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (531065549408668105079/100000000000000000000)
  centralHi := (13276638735216702627/2500000000000000000)
  directionLo := (133352555267905117407/25000000000000000000)
  directionHi := (533410221071620469629/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree115.table
  base := (6172159421922454685135162156718157897997/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-694230922668423283298208474811416705250000000000)
      constant := (21212347338846839017041757963471789431557855257330) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree115.table
  base := (61721593506027681883099133528993572911419/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-694998721612911401876777283748841861500000000000)
      constant := (21258285353770915123426420473920281688628834174291) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (133352555267905117407/25000000000000000000)
  centralHi := (533410221071620469629/100000000000000000000)
  directionLo := (267872315720857732969/50000000000000000000)
  directionHi := (535744631441715465939/100000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree116.table
  base := (7930917034130372033399589830605225610007/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-700265688841848680000789127179763229000000000000)
      constant := (21587520669937542837475809174968986602920207716984) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree116.table
  base := (1982729238399458152098788293928699635401/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-701040164298897564827867230107948604000000000000)
      constant := (21634260945984235323133839969765327138109527446048) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (267872315720857732969/50000000000000000000)
  centralHi := (535744631441715465939/100000000000000000000)
  directionLo := (538068914074734536271/100000000000000000000)
  directionHi := (33629307129670908517/6250000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree117.table
  base := (65194338954761609501317807311951849716983/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34348089235695900023198623234110000000000000)
      linear := (-4179292633226473826647158458864554750000000000)
      constant := (129976259500877264277549304602956690552175034423) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree117.table
  base := (65194338372801792786814592347415834161939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (5329082)
      previous := (2664541)
      next := (2664541)
      square := (34348089235695900023198623234110000000000000)
      linear := (-4183914834230081229461285067852398500000000000)
      constant := (130257617382181815814256785811465092270777657459) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (538068914074734536271/100000000000000000000)
  centralHi := (33629307129670908517/6250000000000000000)
  directionLo := (270191599827098887957/50000000000000000000)
  directionHi := (108076639930839555183/20000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree118.table
  base := (66962602209324213390248227052932007457127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-712335221188699473405950431916456276500000000000)
      constant := (22347748895572553480114365435805076456215925198303) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree118.table
  base := (66962601683665164770307291277900402599323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-713123049670869890730047122826162089000000000000)
      constant := (22396114528182657131661572541325766856499033725747) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (270191599827098887957/50000000000000000000)
  centralHi := (108076639930839555183/20000000000000000000)
  directionLo := (135671904019276659939/25000000000000000000)
  directionHi := (542687616077106639757/100000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree119.table
  base := (68752125987457790829510367052973153547427/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-718369987362124870108531084284802800250000000000)
      constant := (22732803789346692639179412027142890386152459335003) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree119.table
  base := (34376062756337641090886994769354211798727/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-719164492356856053681137069185268831500000000000)
      constant := (22781992517406536860811386709630440510764855601406) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (135671904019276659939/25000000000000000000)
  centralHi := (542687616077106639757/100000000000000000000)
  directionLo := (5449822885364235493/1000000000000000000)
  directionHi := (544982288536423549301/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree120.table
  base := (564503281960506581903452982574735830363/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-724404753535550266811111736653149324000000000000)
      constant := (23121152536645132256431057861204420573903571038375) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree120.table
  base := (35281454908126806390376751548212647987637/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-725205935042842216632227015544375574000000000000)
      constant := (23171171304938665456570385445471575996740814467386) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5449822885364235493/1000000000000000000)
  centralHi := (544982288536423549301/100000000000000000000)
  directionLo := (547267339600438908281/100000000000000000000)
  directionHi := (273633669800219454141/50000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree121.table
  base := (36197477471335533944184835154297929496151/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (7443098)
      previous := (3721549)
      next := (3721549)
      square := (47973777527542207470417911789790000000000000)
      linear := (-6036690245528724491848697429929717750000000000)
      constant := (194320620968400852804327017241146843253448852718) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree121.table
  base := (36197477277700567370030064140118383896349/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (7443098)
      previous := (3721549)
      next := (3721549)
      square := (47973777527542207470417911789790000000000000)
      linear := (-6043366758089490740357991420689936500000000000)
      constant := (194740916450340071643779679874575171935014712282) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (547267339600438908281/100000000000000000000)
  centralHi := (273633669800219454141/50000000000000000000)
  directionLo := (17173215290286496841/3125000000000000000)
  directionHi := (549542889289167898913/100000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree122.table
  base := (74248260044953520134741886403855797083947/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-736474285882401060216273041389842371500000000000)
      constant := (23907731590680014643338516776919040274458387225283) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree122.table
  base := (18562064923804010308676628307114064684833/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-737288820414814542534406908262589059000000000000)
      constant := (23959431273806338253549390112369213906995776624548) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17173215290286496841/3125000000000000000)
  centralHi := (549542889289167898913/100000000000000000000)
  directionLo := (551809055147911797993/100000000000000000000)
  directionHi := (275904527573955898997/50000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree123.table
  base := (3044913020811594774795353939552551559169/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-742509052055826456918853693758188895250000000000)
      constant := (24305961896922238984012713628019583536164045601025) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree123.table
  base := (1903070630111562398746679127836898429331/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-743330263100800705485496854621695801500000000000)
      constant := (24358512454653648486861058180586167635040016098360) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (551809055147911797993/100000000000000000000)
  centralHi := (275904527573955898997/50000000000000000000)
  directionLo := (277032976159055693791/50000000000000000000)
  directionHi := (554065952318111387583/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree124.table
  base := (9752331417547059641035668815192594724249/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-748543818229251853621434346126535419000000000000)
      constant := (24707486055694236233169939868070539641537692609288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree124.table
  base := (78018651055184993779906875439440946706231/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-749371705786786868436586800980802544000000000000)
      constant := (24760894432826709342102591958824500307329654096559) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (277032976159055693791/50000000000000000000)
  centralHi := (554065952318111387583/100000000000000000000)
  directionLo := (278156846802806653223/50000000000000000000)
  directionHi := (556313693605613306447/100000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree125.table
  base := (79935737479878469365502275798879763701057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-754578584402677250324014998494881942750000000000)
      constant := (25112304066808982095810319072042817479807359668073) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree125.table
  base := (39967868611181734206870134731344023334437/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-755413148472773031387676747339909286500000000000)
      constant := (25166577208140820462979657524128137695214531397786) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (278156846802806653223/50000000000000000000)
  centralHi := (556313693605613306447/100000000000000000000)
  directionLo := (69819048693307983269/12500000000000000000)
  directionHi := (558552389546463866153/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree126.table
  base := (5117130244757379736925898766598144589937/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-760613350576102647026595650863228466500000000000)
      constant := (25520415930099067253326198524218763171533285014288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree126.table
  base := (81874083683604811565857661605676571432117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-761454591158759194338766693699016029000000000000)
      constant := (25575560780430673931141984967201658203901745152413) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69819048693307983269/12500000000000000000)
  centralHi := (558552389546463866153/100000000000000000000)
  directionLo := (280391074235169455991/50000000000000000000)
  directionHi := (560782148470338911983/100000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree127.table
  base := (83833690628795814444849362810356861976063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-766648116749528043729176303231574990250000000000)
      constant := (25931821645414639123239597513660289381547700435607) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree127.table
  base := (83833690418866934518478856256547180879807/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-767496033844745357289856640058122771500000000000)
      constant := (25987845149548317263929025001600906729172583576823) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (280391074235169455991/50000000000000000000)
  centralHi := (560782148470338911983/100000000000000000000)
  directionLo := (35187692285107044887/6250000000000000000)
  directionHi := (563003076561712718193/100000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree128.table
  base := (85814557599741038410306906365549329760369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-772682882922953440431756955599921514000000000000)
      constant := (26346521212621560372819429460045488918181392630841) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree128.table
  base := (10726819676276489720214751477984469914769/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-773537476530731520240946586417229514000000000000)
      constant := (26403430315361331143043963964858088812229177379528) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell103.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35187692285107044887/6250000000000000000)
  centralHi := (563003076561712718193/100000000000000000000)
  directionLo := (282607638959431823067/50000000000000000000)
  directionHi := (113043055583772729227/20000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree129.table
  base := (87816684812688734298937789927380922145559/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-778717649096378837134337607968268037750000000000)
      constant := (26764514631599761225647447059743885968110274992751) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 11311
  qDenominator := 21736
  table := BinomialMassData.Q11311_21736.Degree129.table
  base := (8781668464158516449903532547906078157077/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (900614858)
      previous := (450307429)
      next := (450307429)
      square := (5804827080832607103920567326564590000000000000)
      linear := (-779578919216717683192036532776336256500000000000)
      constant := (26822316277751199106075630140450016248683733938530) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q11311_21736.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell103.Kernel129
