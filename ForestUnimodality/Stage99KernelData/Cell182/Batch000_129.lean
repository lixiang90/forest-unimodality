import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell182.Parameters
import ForestUnimodality.BinomialMassData.Q41_63.Batch000_049
import ForestUnimodality.BinomialMassData.Q41_63.Batch050_099
import ForestUnimodality.BinomialMassData.Q41_63.Batch100_149
import ForestUnimodality.BinomialMassData.Q83_126.Batch000_049
import ForestUnimodality.BinomialMassData.Q83_126.Batch050_099
import ForestUnimodality.BinomialMassData.Q83_126.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree000.table
  base := (6874440601623494230256739/1000000000000000000000000)
  polynomial :=
    { denominator := 31500000000000000000000000000000000000000
      center := (41)
      previous := (0)
      next := (22)
      square := (1147362297528167100063578601000000000000)
      linear := (-2308073751328987240072354566000000000000)
      constant := (216544878951140068253087278500000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree000.table
  base := (6874440601623494230256739/1000000000000000000000000)
  polynomial :=
    { denominator := 63000000000000000000000000000000000000000
      center := (83)
      previous := (0)
      next := (43)
      square := (2294724595056334200127157202000000000000)
      linear := (-4616147502657974480144709132000000000000)
      constant := (433089757902280136506174557000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree001.table
  base := (10036185790840896164048400905456424792139/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7938000000000000000000000000000000000000000
      center := (10332)
      previous := (0)
      next := (5544)
      square := (289135298977098109216021807452000000000000)
      linear := (-957969418924143593319087131760000000000000)
      constant := (40334603659201651664715326525328549999999691) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree001.table
  base := (49958690648376345567442776695536092214663/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (52290)
      previous := (0)
      next := (27090)
      square := (1445676494885490546080109037260000000000000)
      linear := (-4812794340571281308596707230820000000000000)
      constant := (200829060180157310137260910627877749999997447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (30184421155165788947/100000000000000000000)
  directionHi := (7546105288791447237/25000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree002.table
  base := (18181934720109090241394067351844419249181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (25830)
      previous := (0)
      next := (13860)
      square := (722838247442745273040054518630000000000000)
      linear := (-3335760631283456005349852282220000000000000)
      constant := (75281300981564557527305955891070499999999389) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree002.table
  base := (2252237710606873801493377279742079239103/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (26145)
      previous := (0)
      next := (13545)
      square := (722838247442745273040054518630000000000000)
      linear := (-3358707877234019347351123854240000000000000)
      constant := (74683384567089586695918720943180499999998456) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30184421155165788947/100000000000000000000)
  centralHi := (7546105288791447237/25000000000000000000)
  directionLo := (10671804442504205793/25000000000000000000)
  directionHi := (42687217770016823173/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree003.table
  base := (6514610918576471023616304042301272610749/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1102500000000000000000000000000000000000000
      center := (1435)
      previous := (0)
      next := (770)
      square := (40157680413485848502225251035000000000000)
      linear := (-237588761958697390411221485280000000000000)
      constant := (3183734488269930618947264123099861221340309) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree003.table
  base := (513904542154730860864119545707826228669/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 441000000000000000000000000000000000000000
      center := (581)
      previous := (0)
      next := (301)
      square := (16063072165394339400890100414000000000000)
      linear := (-95800412981831067564530979846000000000000)
      constant := (1259747800886137045596099637963256834215145) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10671804442504205793/25000000000000000000)
  centralHi := (42687217770016823173/100000000000000000000)
  directionLo := (52280951037804008779/100000000000000000000)
  directionHi := (2614047551890200439/5000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree004.table
  base := (146810142257272949425872632398778401597/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7938000000000000000000000000000000000000000
      center := (10332)
      previous := (0)
      next := (5544)
      square := (289135298977098109216021807452000000000000)
      linear := (-2086973919691860019781648475144000000000000)
      constant := (18040663308528618152035391469032786898462325) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree004.table
  base := (1124613465988842001213000032764722581361/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (26145)
      previous := (0)
      next := (13545)
      square := (722838247442745273040054518630000000000000)
      linear := (-5263329291130776733456664331900000000000000)
      constant := (44558655464472111407599090688025471403374472) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52280951037804008779/100000000000000000000)
  centralHi := (2614047551890200439/5000000000000000000)
  directionLo := (12073768462066315579/20000000000000000000)
  directionHi := (7546105288791447237/12500000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree005.table
  base := (12575296679704971271267043701439300241369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (51660)
      previous := (0)
      next := (27720)
      square := (1445676494885490546080109037260000000000000)
      linear := (-12316543766405494143012511281360000000000000)
      constant := (74681724919220488939375198015112582657993561) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree005.table
  base := (12245502829588221515815489809420738216451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (52290)
      previous := (0)
      next := (27090)
      square := (1445676494885490546080109037260000000000000)
      linear := (-12431279996158310853018869141460000000000000)
      constant := (73863801377364327513083841340365909981094019) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12073768462066315579/20000000000000000000)
  centralHi := (7546105288791447237/12500000000000000000)
  directionLo := (67494417564433431477/100000000000000000000)
  directionHi := (33747208782216715739/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree006.table
  base := (4125607538554916726654478408138454617311/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (2870)
      previous := (0)
      next := (1540)
      square := (80315360826971697004450502070000000000000)
      linear := (-788789885241760454839821121500000000000000)
      constant := (3674848017894450277761307053509058486234151) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree006.table
  base := (7959110151502949173739656180822631434293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5810)
      previous := (0)
      next := (3010)
      square := (160630721653943394008901004140000000000000)
      linear := (-1592877934450563137680489957680000000000000)
      constant := (7296364851808980875074460436322780462523213) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67494417564433431477/100000000000000000000)
  centralHi := (33747208782216715739/50000000000000000000)
  directionLo := (18484107502856541973/25000000000000000000)
  directionHi := (73936430011426167893/100000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree007.table
  base := (4985510679890294316595522879145212729063/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (7380)
      previous := (0)
      next := (3960)
      square := (206525213555070078011444148180000000000000)
      linear := (-2297127443185411747317292727520000000000000)
      constant := (9005440636353897292606493612775335617378721) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree007.table
  base := (946794788804751027452691648862632967613/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1134000000000000000000000000000000000000000
      center := (1494)
      previous := (0)
      next := (774)
      square := (41305042711014015602288829636000000000000)
      linear := (-464014937827195017863712859908000000000000)
      constant := (1798214984380854953566352909782112892636571) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18484107502856541973/25000000000000000000)
  centralHi := (73936430011426167893/100000000000000000000)
  directionLo := (79860471845005650117/100000000000000000000)
  directionHi := (39930235922502825059/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree008.table
  base := (1252634667856231613950735703719997503451/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (25830)
      previous := (0)
      next := (13860)
      square := (722838247442745273040054518630000000000000)
      linear := (-8980783135122038137662658999140000000000000)
      constant := (32135494522869402580864942224224670091197019) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree008.table
  base := (458617345041317357747054569244294745277/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7938000000000000000000000000000000000000000
      center := (10458)
      previous := (0)
      next := (5418)
      square := (289135298977098109216021807452000000000000)
      linear := (-3629028847569716602267098114888000000000000)
      constant := (12915016208535133834216234557970605844004413) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79860471845005650117/100000000000000000000)
  centralHi := (39930235922502825059/50000000000000000000)
  directionLo := (10671804442504205793/12500000000000000000)
  directionHi := (17074887108006729269/20000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree009.table
  base := (304236379113213013047514591223839597923/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (2870)
      previous := (0)
      next := (1540)
      square := (80315360826971697004450502070000000000000)
      linear := (-1102402246566126128857199272440000000000000)
      constant := (3835787084297881557479155918619713262684043) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree009.table
  base := (216141755380047935955577839628970745477/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (2905)
      previous := (0)
      next := (1505)
      square := (80315360826971697004450502070000000000000)
      linear := (-1113875869541407799857835058450000000000000)
      constant := (3876090145092539113078577322983876098755357) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10671804442504205793/12500000000000000000)
  centralHi := (17074887108006729269/20000000000000000000)
  directionLo := (90553263465497366843/100000000000000000000)
  directionHi := (22638315866374341711/25000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree010.table
  base := (-854365662128521178142782954503448269259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (51660)
      previous := (0)
      next := (27720)
      square := (1445676494885490546080109037260000000000000)
      linear := (-21724914606136464363533855809560000000000000)
      constant := (76764307516000035930223193268775813819311029) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree010.table
  base := (-499430635695780128192151577803442169321/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (26145)
      previous := (0)
      next := (13545)
      square := (722838247442745273040054518630000000000000)
      linear := (-10977193532821048891773285764880000000000000)
      constant := (38962055032365504258529403512348138029964951) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90553263465497366843/100000000000000000000)
  centralHi := (22638315866374341711/25000000000000000000)
  directionLo := (5965720044005912541/6250000000000000000)
  directionHi := (95451520704094600657/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree011.table
  base := (-1993843203558286882265619547936087988751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (51660)
      previous := (0)
      next := (27720)
      square := (1445676494885490546080109037260000000000000)
      linear := (-23606588774082658407638124715200000000000000)
      constant := (86992448444454058022131489762101666772647281) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree011.table
  base := (-2111161504447817808653759687701281608173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (52290)
      previous := (0)
      next := (27090)
      square := (1445676494885490546080109037260000000000000)
      linear := (-23859008479538855169652112007420000000000000)
      constant := (88598723099453020288591376642408613297161363) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5965720044005912541/6250000000000000000)
  centralHi := (95451520704094600657/100000000000000000000)
  directionLo := (25027599871437707727/25000000000000000000)
  directionHi := (100110399485750830909/100000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree012.table
  base := (-2891778170850166846419776054391834333613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5740)
      previous := (0)
      next := (3080)
      square := (160630721653943394008901004140000000000000)
      linear := (-2832029215780983605749154846760000000000000)
      constant := (11044872605669239715369894372013201058876667) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree012.table
  base := (-2986243713490340210282504308171218513389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5810)
      previous := (0)
      next := (3010)
      square := (160630721653943394008901004140000000000000)
      linear := (-2862625543715068061750850276120000000000000)
      constant := (11274387337531401912739764789376492635595451) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25027599871437707727/25000000000000000000)
  centralHi := (100110399485750830909/100000000000000000000)
  directionLo := (52280951037804008779/50000000000000000000)
  directionHi := (104561902075608017559/100000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree013.table
  base := (-3608695698432481977366401930564244526599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (51660)
      previous := (0)
      next := (27720)
      square := (1445676494885490546080109037260000000000000)
      linear := (-27369937109975046495846662526480000000000000)
      constant := (113758298277161328499880869833210513473928569) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree013.table
  base := (-184211596352883816537735978401322829223/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3969000000000000000000000000000000000000000
      center := (5229)
      previous := (0)
      next := (2709)
      square := (144567649488549054608010903726000000000000)
      linear := (-2766825130733236994186319296274000000000000)
      constant := (11629776661045029883227560586567799381627826) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52280951037804008779/50000000000000000000)
  centralHi := (104561902075608017559/100000000000000000000)
  directionLo := (108831478195150231411/100000000000000000000)
  directionHi := (27207869548787557853/25000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree014.table
  base := (-83787359252456807088715236156934000793/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 567000000000000000000000000000000000000000
      center := (738)
      previous := (0)
      next := (396)
      square := (20652521355507007801144414818000000000000)
      linear := (-417880161113160579142156163316000000000000)
      constant := (1855401173643771210570359012791092107751845) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree014.table
  base := (-6639704204556712423224972487474299751/15625000000000000000000000000000000000)
  polynomial :=
    { denominator := 567000000000000000000000000000000000000000
      center := (747)
      previous := (0)
      next := (387)
      square := (20652521355507007801144414818000000000000)
      linear := (-422469610303273247542410477720000000000000)
      constant := (1898682849361556379735354830172532610635712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108831478195150231411/100000000000000000000)
  centralHi := (27207869548787557853/25000000000000000000)
  directionLo := (56469881190360849501/50000000000000000000)
  directionHi := (112939762380721699003/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree015.table
  base := (-1166728397122871142942865316928013946541/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1102500000000000000000000000000000000000000
      center := (1435)
      previous := (0)
      next := (770)
      square := (40157680413485848502225251035000000000000)
      linear := (-864813484607428738445977787160000000000000)
      constant := (4100882146161870369508496166159745849575419) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree015.table
  base := (-4714397309854250029267704269483666091533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5810)
      previous := (0)
      next := (3010)
      square := (160630721653943394008901004140000000000000)
      linear := (-3497499348347320523786030435340000000000000)
      constant := (16796680721072754023038257071332703253633947) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56469881190360849501/50000000000000000000)
  centralHi := (112939762380721699003/100000000000000000000)
  directionLo := (2922594011221698527/2500000000000000000)
  directionHi := (116903760448867941081/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree016.table
  base := (-5065830588863106311655836614635785431169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (51660)
      previous := (0)
      next := (27720)
      square := (1445676494885490546080109037260000000000000)
      linear := (-33014959613813628628159469243400000000000000)
      constant := (166922090984550172900044470299870567623690239) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree016.table
  base := (-51032154048467801304135922386055003067/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3969000000000000000000000000000000000000000
      center := (5229)
      previous := (0)
      next := (2709)
      square := (144567649488549054608010903726000000000000)
      linear := (-3338211554902264210017981439572000000000000)
      constant := (17098939796183708394059108322129476928270770) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2922594011221698527/2500000000000000000)
  centralHi := (116903760448867941081/100000000000000000000)
  directionLo := (12073768462066315579/10000000000000000000)
  directionHi := (120737684620663155791/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree017.table
  base := (-337765007349451829416165084683534069681/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9922500000000000000000000000000000000000000
      center := (12915)
      previous := (0)
      next := (6930)
      square := (361419123721372636520027259315000000000000)
      linear := (-8724158445439955668065934537260000000000000)
      constant := (46919290115896966995363901045789213109744444) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree017.table
  base := (-271677947365690449691725387634556063871/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3969000000000000000000000000000000000000000
      center := (5229)
      previous := (0)
      next := (2709)
      square := (144567649488549054608010903726000000000000)
      linear := (-3528673696291939948628535487338000000000000)
      constant := (19229538649929016642800921974166393964992002) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12073768462066315579/10000000000000000000)
  centralHi := (120737684620663155791/100000000000000000000)
  directionLo := (3889173645964899637/3125000000000000000)
  directionHi := (24890711334175357677/20000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree018.table
  base := (-1139109262091310306344762317108437685441/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882000000000000000000000000000000000000000
      center := (1148)
      previous := (0)
      next := (616)
      square := (32126144330788678801780200828000000000000)
      linear := (-817295732215689260363733490104000000000000)
      constant := (4663194770756151730118550694731178980720519) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree018.table
  base := (-1143691982113081821598812793504093288553/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882000000000000000000000000000000000000000
      center := (1162)
      previous := (0)
      next := (602)
      square := (32126144330788678801780200828000000000000)
      linear := (-826474630595914597164242118912000000000000)
      constant := (4778585959998807910286369835284694859748127) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3889173645964899637/3125000000000000000)
  centralHi := (24890711334175357677/20000000000000000000)
  directionLo := (32015413327512617379/25000000000000000000)
  directionHi := (128061653310050469517/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree019.table
  base := (-2974832065928012996565167721882526230933/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (25830)
      previous := (0)
      next := (13860)
      square := (722838247442745273040054518630000000000000)
      linear := (-19329991058826105380236137980160000000000000)
      constant := (116691275576087773234206348811058253389426923) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree019.table
  base := (-5967516597630388744132508118526926014779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (52290)
      previous := (0)
      next := (27090)
      square := (1445676494885490546080109037260000000000000)
      linear := (-39095979790712914258496435828700000000000000)
      constant := (239174247399084312516670810482301630647342149) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32015413327512617379/25000000000000000000)
  centralHi := (128061653310050469517/100000000000000000000)
  directionLo := (65785420742319457321/50000000000000000000)
  directionHi := (131570841484638914643/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree020.table
  base := (-1234785527712140861685734102942789484893/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7938000000000000000000000000000000000000000
      center := (10332)
      previous := (0)
      next := (5544)
      square := (289135298977098109216021807452000000000000)
      linear := (-8108331257119680960915308973192000000000000)
      constant := (51652882199341943961549517421100068534459683) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree020.table
  base := (-3093899180110865526903569219440761226739/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (26145)
      previous := (0)
      next := (13545)
      square := (722838247442745273040054518630000000000000)
      linear := (-20500300602304835822300988153180000000000000)
      constant := (132340482919877602980415403368839618691072909) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65785420742319457321/50000000000000000000)
  centralHi := (131570841484638914643/100000000000000000000)
  directionLo := (67494417564433431477/50000000000000000000)
  directionHi := (26997767025773372591/20000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree021.table
  base := (-3186880914919154462200448392459355465559/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 315000000000000000000000000000000000000000
      center := (410)
      previous := (0)
      next := (220)
      square := (11473622975281671000635786010000000000000)
      linear := (-336693098837655546418101696600000000000000)
      constant := (2257681050758220297476677573385060605669783) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree021.table
  base := (-399031997122137907964737104162935756953/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 315000000000000000000000000000000000000000
      center := (415)
      previous := (0)
      next := (215)
      square := (11473622975281671000635786010000000000000)
      linear := (-340517639829416103418313625270000000000000)
      constant := (2313776650070825493800779598434380378495688) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67494417564433431477/50000000000000000000)
  centralHi := (26997767025773372591/20000000000000000000)
  directionLo := (138322394751973624287/100000000000000000000)
  directionHi := (4322574835999175759/3125000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree022.table
  base := (-1638294903447964817287582390715121674139/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9922500000000000000000000000000000000000000
      center := (12915)
      previous := (0)
      next := (6930)
      square := (361419123721372636520027259315000000000000)
      linear := (-11076251155372698223196270669310000000000000)
      constant := (77994207029098193845303000146451682075342309) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree022.table
  base := (-6561492324295942309274875379302770602741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (52290)
      previous := (0)
      next := (27090)
      square := (1445676494885490546080109037260000000000000)
      linear := (-44809844032403186416813057261680000000000000)
      constant := (319723702708027734655319420615967303477720971) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (138322394751973624287/100000000000000000000)
  centralHi := (4322574835999175759/3125000000000000000)
  directionLo := (35394371171834336301/25000000000000000000)
  directionHi := (28315496937467469041/20000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree023.table
  base := (-3357574704221673504727777288700660458577/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (25830)
      previous := (0)
      next := (13860)
      square := (722838247442745273040054518630000000000000)
      linear := (-23093339394718493468444675791440000000000000)
      constant := (170389838254075744289877629682757078639907887) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree023.table
  base := (-1680391019437308413922438562785308533157/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (26145)
      previous := (0)
      next := (13545)
      square := (722838247442745273040054518630000000000000)
      linear := (-23357232723149971901459298869670000000000000)
      constant := (174616644686929381698790112085797720863799734) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35394371171834336301/25000000000000000000)
  centralHi := (28315496937467469041/20000000000000000000)
  directionLo := (144759398488891423273/100000000000000000000)
  directionHi := (72379699244445711637/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree024.table
  base := (-6861867050117858529674255424451369141637/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5740)
      previous := (0)
      next := (3080)
      square := (160630721653943394008901004140000000000000)
      linear := (-5340928106375908997888180054280000000000000)
      constant := (41207515810715292135352833821496946208538083) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree024.table
  base := (-10986892333271099763924171417261968939/16000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882000000000000000000000000000000000000000
      center := (1162)
      previous := (0)
      next := (602)
      square := (32126144330788678801780200828000000000000)
      linear := (-1080424152448815581978314182600000000000000)
      constant := (8445696898351312496954463780831433962237625) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (144759398488891423273/100000000000000000000)
  centralHi := (72379699244445711637/50000000000000000000)
  directionLo := (18484107502856541973/12500000000000000000)
  directionHi := (29574572004570467157/20000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree025.table
  base := (-5595965534361976207428585869765563727/8000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3969000000000000000000000000000000000000000
      center := (5166)
      previous := (0)
      next := (2772)
      square := (144567649488549054608010903726000000000000)
      linear := (-4995002712532937502509788939416000000000000)
      constant := (40223427832045614094786939304412559695942125) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree025.table
  base := (-6998755673733930319931972391169718769767/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (52290)
      previous := (0)
      next := (27090)
      square := (1445676494885490546080109037260000000000000)
      linear := (-50523708274093458575129678694660000000000000)
      constant := (412186833538860997554488629770822386202794777) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18484107502856541973/12500000000000000000)
  centralHi := (29574572004570467157/20000000000000000000)
  directionLo := (75461052887914472369/50000000000000000000)
  directionHi := (150922105775828944739/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree026.table
  base := (-7115620700151819794746232133030548627671/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (51660)
      previous := (0)
      next := (27720)
      square := (1445676494885490546080109037260000000000000)
      linear := (-51831701293275569069202158299800000000000000)
      constant := (434874815079722817148502081699361752496773801) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree026.table
  base := (-3559268402656893608832180978564372136347/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (26145)
      previous := (0)
      next := (13545)
      square := (722838247442745273040054518630000000000000)
      linear := (-26214164843995107980617609586160000000000000)
      constant := (222810114190899449324246543591288006990838757) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75461052887914472369/50000000000000000000)
  centralHi := (150922105775828944739/100000000000000000000)
  directionLo := (76955476238346612779/50000000000000000000)
  directionHi := (153910952476693225559/100000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree027.table
  base := (-225773357238575080738539937332861075459/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1102500000000000000000000000000000000000000
      center := (1435)
      previous := (0)
      next := (770)
      square := (40157680413485848502225251035000000000000)
      linear := (-1492038207256160086480734089040000000000000)
      constant := (13021825666517948594128843912414666125780648) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree027.table
  base := (-3613491332149156813276149773983736543799/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (2905)
      previous := (0)
      next := (1505)
      square := (80315360826971697004450502070000000000000)
      linear := (-3018497283438165185963375536110000000000000)
      constant := (26686291360442485377464562541700672184184641) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76955476238346612779/50000000000000000000)
  centralHi := (153910952476693225559/100000000000000000000)
  directionLo := (156842853113412026337/100000000000000000000)
  directionHi := (78421426556706013169/50000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree028.table
  base := (-3661497442473936323547033855827176694099/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2835000000000000000000000000000000000000000
      center := (3690)
      previous := (0)
      next := (1980)
      square := (103262606777535039005722074090000000000000)
      linear := (-3971074973511996939815049722220000000000000)
      constant := (35997456740427464204167504461425990814445867) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree028.table
  base := (-1831176468084564682303376480069035874959/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2835000000000000000000000000000000000000000
      center := (3735)
      previous := (0)
      next := (1935)
      square := (103262606777535039005722074090000000000000)
      linear := (-4016969465413123623817592866260000000000000)
      constant := (36884532168716192034734715128001713317796494) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156842853113412026337/100000000000000000000)
  centralHi := (78421426556706013169/50000000000000000000)
  directionLo := (79860471845005650117/50000000000000000000)
  directionHi := (31944188738002260047/20000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree029.table
  base := (-1482169954392404610693797544470748195197/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7938000000000000000000000000000000000000000
      center := (10332)
      previous := (0)
      next := (5544)
      square := (289135298977098109216021807452000000000000)
      linear := (-11495344759422830240302993003344000000000000)
      constant := (108081778886865331373875826552959600413263107) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree029.table
  base := (-3706078900297597195882461019261180927999/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (26145)
      previous := (0)
      next := (13545)
      square := (722838247442745273040054518630000000000000)
      linear := (-29071096964840244059775920302650000000000000)
      constant := (276854527255922237493823303309419872896771969) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79860471845005650117/50000000000000000000)
  centralHi := (31944188738002260047/20000000000000000000)
  directionLo := (162548082528525019217/100000000000000000000)
  directionHi := (81274041264262509609/50000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree030.table
  base := (-7488672272565373321459720226901295682221/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5740)
      previous := (0)
      next := (3080)
      square := (160630721653943394008901004140000000000000)
      linear := (-6595377551673371693957692658040000000000000)
      constant := (64235310516188343272445957234336528604140539) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree030.table
  base := (-748967105673941274420447837409745851543/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 441000000000000000000000000000000000000000
      center := (581)
      previous := (0)
      next := (301)
      square := (16063072165394339400890100414000000000000)
      linear := (-667186837150858283396193123144000000000000)
      constant := (6581430409084163409272023602112302079469537) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (162548082528525019217/100000000000000000000)
  centralHi := (81274041264262509609/50000000000000000000)
  directionLo := (5166465109975139501/3125000000000000000)
  directionHi := (165326883519204464033/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree031.table
  base := (-1889182242653687980109793311267861017207/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9922500000000000000000000000000000000000000
      center := (12915)
      previous := (0)
      next := (6930)
      square := (361419123721372636520027259315000000000000)
      linear := (-15310018033251634822430875707000000000000000)
      constant := (154272509232190511102826859390542859622705417) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree031.table
  base := (-188937269394141212872056031609463597489/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3969000000000000000000000000000000000000000
      center := (5229)
      previous := (0)
      next := (2709)
      square := (144567649488549054608010903726000000000000)
      linear := (-6195143675747400289176292156062000000000000)
      constant := (63224152433842328188997115121277655926264636) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5166465109975139501/3125000000000000000)
  centralHi := (165326883519204464033/100000000000000000000)
  directionLo := (168059744420384683169/100000000000000000000)
  directionHi := (16805974442038468317/10000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree032.table
  base := (-95190215189991303890577300153343513907/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1984500000000000000000000000000000000000000
      center := (2583)
      previous := (0)
      next := (1386)
      square := (72283824744274527304005451863000000000000)
      linear := (-3156087315047636666691388586682000000000000)
      constant := (32866241900249635170659562756845518373212468) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree032.table
  base := (-7615797665006970762595720336008188289123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (52290)
      previous := (0)
      next := (27090)
      square := (1445676494885490546080109037260000000000000)
      linear := (-63856058171370760277868462038280000000000000)
      constant := (673446699846985249059746371978703500680470813) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (168059744420384683169/100000000000000000000)
  centralHi := (16805974442038468317/10000000000000000000)
  directionLo := (10671804442504205793/6250000000000000000)
  directionHi := (170748871080067292689/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree033.table
  base := (-3832141569795011241392248379778725191347/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (2870)
      previous := (0)
      next := (1540)
      square := (80315360826971697004450502070000000000000)
      linear := (-3611301137161051520996224479960000000000000)
      constant := (38823423215079694402983672610007582190615973) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree033.table
  base := (-3832362488143920675265812744446175406701/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (2905)
      previous := (0)
      next := (1505)
      square := (80315360826971697004450502070000000000000)
      linear := (-3653371088070417647998555695330000000000000)
      constant := (39774651914820517733823318605286736645644859) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10671804442504205793/6250000000000000000)
  centralHi := (170748871080067292689/100000000000000000000)
  directionLo := (43349074568834411197/25000000000000000000)
  directionHi := (173396298275337644789/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree034.table
  base := (-963004373635380013230614203495224464889/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9922500000000000000000000000000000000000000
      center := (12915)
      previous := (0)
      next := (6930)
      square := (361419123721372636520027259315000000000000)
      linear := (-16721273659211280355509077386230000000000000)
      constant := (185394986725626769348370824848534908197711118) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree034.table
  base := (-7704371005565880125589031996449594897259/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (52290)
      previous := (0)
      next := (27090)
      square := (1445676494885490546080109037260000000000000)
      linear := (-67665300999164275050079542993600000000000000)
      constant := (759732238061119699164848810201951557852779029) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43349074568834411197/25000000000000000000)
  centralHi := (173396298275337644789/100000000000000000000)
  directionLo := (44000976932380632591/25000000000000000000)
  directionHi := (35200781545904506073/20000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree035.table
  base := (-3867276489535570268795865365348184790777/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2835000000000000000000000000000000000000000
      center := (3690)
      previous := (0)
      next := (1980)
      square := (103262606777535039005722074090000000000000)
      linear := (-4911912057485093961867184175040000000000000)
      constant := (56114250480236891477709838650397579223629441) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree035.table
  base := (-7734808298696100932422478500223434403291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (7470)
      previous := (0)
      next := (3870)
      square := (206525213555070078011444148180000000000000)
      linear := (-9938560344723004633740726210180000000000000)
      constant := (114973131813648262711199962004398312693334003) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44000976932380632591/25000000000000000000)
  centralHi := (35200781545904506073/20000000000000000000)
  directionLo := (178573443760640682589/100000000000000000000)
  directionHi := (17857344376064068259/10000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree036.table
  base := (-1938974146677920614720113672615553514001/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1102500000000000000000000000000000000000000
      center := (1435)
      previous := (0)
      next := (770)
      square := (40157680413485848502225251035000000000000)
      linear := (-1962456749242708597506801315450000000000000)
      constant := (23080001701917365348132053509136540900325559) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree036.table
  base := (-3878045215679195594396366004916167987387/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (2905)
      previous := (0)
      next := (1505)
      square := (80315360826971697004450502070000000000000)
      linear := (-3970807990386543879016145774940000000000000)
      constant := (47287920873786125860465556784471969917562333) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (178573443760640682589/100000000000000000000)
  centralHi := (17857344376064068259/10000000000000000000)
  directionLo := (90553263465497366843/50000000000000000000)
  directionHi := (181106526930994733687/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree037.table
  base := (-1553621988873906455177906563955790920161/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7938000000000000000000000000000000000000000
      center := (10332)
      previous := (0)
      next := (5544)
      square := (289135298977098109216021807452000000000000)
      linear := (-14506023428136740710869823252368000000000000)
      constant := (175484287075655387632361919536159465837880991) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree037.table
  base := (-388412850121968577569195672949231727041/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3969000000000000000000000000000000000000000
      center := (5229)
      previous := (0)
      next := (2709)
      square := (144567649488549054608010903726000000000000)
      linear := (-7337916524085454720839616442658000000000000)
      constant := (89884403999097598130841039848518498550748542) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90553263465497366843/50000000000000000000)
  centralHi := (181106526930994733687/100000000000000000000)
  directionLo := (91802333000691682819/50000000000000000000)
  directionHi := (183604666001383365639/100000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree038.table
  base := (-7771225829052353427555738018063107320447/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (51660)
      previous := (0)
      next := (27720)
      square := (1445676494885490546080109037260000000000000)
      linear := (-74411791308629897598453385167480000000000000)
      constant := (925223498959128421385964703523427527045145857) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree038.table
  base := (-971417163961044330590979398077717917163/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (26145)
      previous := (0)
      next := (13545)
      square := (722838247442745273040054518630000000000000)
      linear := (-37641893327375652297250852452120000000000000)
      constant := (473898099596654982315862049979768150347120212) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91802333000691682819/50000000000000000000)
  centralHi := (183604666001383365639/100000000000000000000)
  directionLo := (46517317110104249321/25000000000000000000)
  directionHi := (37213853688083399457/20000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree039.table
  base := (-3882634306691783326861401322537391170429/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (2870)
      previous := (0)
      next := (1540)
      square := (80315360826971697004450502070000000000000)
      linear := (-4238525859809782869030980781840000000000000)
      constant := (54127008626479846960487748340051010493840811) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree039.table
  base := (-3882676534195361288106846989651394575477/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (2905)
      previous := (0)
      next := (1505)
      square := (80315360826971697004450502070000000000000)
      linear := (-4288244892702670110033735854550000000000000)
      constant := (55446609287277696326338522470771234992214643) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46517317110104249321/25000000000000000000)
  centralHi := (37213853688083399457/20000000000000000000)
  directionLo := (188501649696824618569/100000000000000000000)
  directionHi := (18850164969682461857/10000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree040.table
  base := (-775025644848540106618520400134603466681/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3969000000000000000000000000000000000000000
      center := (5166)
      previous := (0)
      next := (2772)
      square := (144567649488549054608010903726000000000000)
      linear := (-7817513964452228568666192297876000000000000)
      constant := (102460933228899928252554161706745758840743111) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree040.table
  base := (-7750320386422427843221217342193136395019/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (52290)
      previous := (0)
      next := (27090)
      square := (1445676494885490546080109037260000000000000)
      linear := (-79093029482544819366712785859560000000000000)
      constant := (1049572279968068033573418173584035441648169589) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188501649696824618569/100000000000000000000)
  centralHi := (18850164969682461857/10000000000000000000)
  directionLo := (5965720044005912541/3125000000000000000)
  directionHi := (190903041408189201313/100000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree041.table
  base := (-7726202878749769164792764685236622342021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (51660)
      previous := (0)
      next := (27720)
      square := (1445676494885490546080109037260000000000000)
      linear := (-80056813812468479730766191884400000000000000)
      constant := (1076192976238523032384347198470155845924518651) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree041.table
  base := (-1545250250750123501127225009886931602721/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7938000000000000000000000000000000000000000
      center := (10458)
      previous := (0)
      next := (5418)
      square := (289135298977098109216021807452000000000000)
      linear := (-16199530179288315350563665267444000000000000)
      constant := (220479218000855371409802397099697768468800351) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (5965720044005912541/3125000000000000000)
  centralHi := (190903041408189201313/100000000000000000000)
  directionLo := (193274598691522888013/100000000000000000000)
  directionHi := (96637299345761444007/50000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree042.table
  base := (-7693118036407518910284136184824325544119/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (820)
      previous := (0)
      next := (440)
      square := (22947245950563342001271572020000000000000)
      linear := (-1300610920324042440870959695080000000000000)
      constant := (17921222966831496179508325501156067490720503) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree042.table
  base := (-7693154614881949157354657446533333797837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (830)
      previous := (0)
      next := (430)
      square := (22947245950563342001271572020000000000000)
      linear := (-1315909084291084668871807409760000000000000)
      constant := (18357307329823461592233343845808399970736269) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (193274598691522888013/100000000000000000000)
  centralHi := (96637299345761444007/50000000000000000000)
  directionLo := (97808703319083063177/50000000000000000000)
  directionHi := (39123481327633225271/20000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree043.table
  base := (-1912752381323880062385034427064180742181/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9922500000000000000000000000000000000000000
      center := (12915)
      previous := (0)
      next := (6930)
      square := (361419123721372636520027259315000000000000)
      linear := (-20955040537090216954743682423920000000000000)
      constant := (295785378531238606620100892484587266634283611) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree043.table
  base := (-1530207433651689209952423437769738078653/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7938000000000000000000000000000000000000000
      center := (10458)
      previous := (0)
      next := (5418)
      square := (289135298977098109216021807452000000000000)
      linear := (-16961378744847018305005881458508000000000000)
      constant := (242383013741151062614747187541446909565826243) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97808703319083063177/50000000000000000000)
  centralHi := (39123481327633225271/20000000000000000000)
  directionLo := (197932486116640440931/100000000000000000000)
  directionHi := (49483121529160110233/25000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree044.table
  base := (-1519976614947350577032672380297166260659/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7938000000000000000000000000000000000000000
      center := (10332)
      previous := (0)
      next := (5544)
      square := (289135298977098109216021807452000000000000)
      linear := (-17140367263261412372615799720264000000000000)
      constant := (247701271028510125491770939670984547111444429) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree044.table
  base := (-7599903953718670296620860990392520931381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (52290)
      previous := (0)
      next := (27090)
      square := (1445676494885490546080109037260000000000000)
      linear := (-86711515138131848911134947770200000000000000)
      constant := (1268610190781789302308595017964492084423348811) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (197932486116640440931/100000000000000000000)
  centralHi := (49483121529160110233/25000000000000000000)
  directionLo := (25027599871437707727/12500000000000000000)
  directionHi := (200220798971501661817/100000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree045.table
  base := (-7539743023380590020060705886234731966213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5740)
      previous := (0)
      next := (3080)
      square := (160630721653943394008901004140000000000000)
      linear := (-9731501164917028434131474167440000000000000)
      constant := (143903505860341500000226713016270483202900067) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree045.table
  base := (-7539758785344534951140956390086865724569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5810)
      previous := (0)
      next := (3010)
      square := (160630721653943394008901004140000000000000)
      linear := (-9846237394669845144137832027540000000000000)
      constant := (147399523652098770567454127221746692215465071) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25027599871437707727/12500000000000000000)
  centralHi := (200220798971501661817/100000000000000000000)
  directionLo := (202483252693300294431/100000000000000000000)
  directionHi := (6327601646665634201/3125000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree046.table
  base := (-1867648169316985946126636027325619612731/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9922500000000000000000000000000000000000000
      center := (12915)
      previous := (0)
      next := (6930)
      square := (361419123721372636520027259315000000000000)
      linear := (-22366296163049862487821884103150000000000000)
      constant := (338254273451211665966225433533384615757070661) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree046.table
  base := (-373530228521710268684250421288656942309/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3969000000000000000000000000000000000000000
      center := (5229)
      previous := (0)
      next := (2709)
      square := (144567649488549054608010903726000000000000)
      linear := (-9052075796592536368334602872552000000000000)
      constant := (138587162342798779315393313940572641191951158) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (202483252693300294431/100000000000000000000)
  centralHi := (6327601646665634201/3125000000000000000)
  directionLo := (102360352311980785991/50000000000000000000)
  directionHi := (204720704623961571983/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree047.table
  base := (-3696217287430333475401364018837304352907/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (25830)
      previous := (0)
      next := (13860)
      square := (722838247442745273040054518630000000000000)
      linear := (-45673429410072821997695902659120000000000000)
      constant := (706081484126357512697086300421884739023312117) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree047.table
  base := (-739244354460423116426144851657417070081/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3969000000000000000000000000000000000000000
      center := (5229)
      previous := (0)
      next := (2709)
      square := (144567649488549054608010903726000000000000)
      linear := (-9242537937982212106945156920318000000000000)
      constant := (144643791358592379108669953689201211648848511) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (102360352311980785991/50000000000000000000)
  centralHi := (204720704623961571983/100000000000000000000)
  directionLo := (20693396575285493953/10000000000000000000)
  directionHi := (206933965752854939531/100000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree048.table
  base := (-7305270683250231751885977511994866580507/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5740)
      previous := (0)
      next := (3080)
      square := (160630721653943394008901004140000000000000)
      linear := (-10358725887565759782166230469320000000000000)
      constant := (163618796475476947921925241803290263837996413) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree048.table
  base := (-7305277445116627637013062571764837100951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5810)
      previous := (0)
      next := (3010)
      square := (160630721653943394008901004140000000000000)
      linear := (-10481111199302097606173012186760000000000000)
      constant := (167588286271944887791505957797851706838480609) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20693396575285493953/10000000000000000000)
  centralHi := (206933965752854939531/100000000000000000000)
  directionLo := (52280951037804008779/25000000000000000000)
  directionHi := (209123804151216035117/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree049.table
  base := (-7209102543455894943278212717882933432463/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (7380)
      previous := (0)
      next := (3960)
      square := (206525213555070078011444148180000000000000)
      linear := (-13587172450862576011942906161360000000000000)
      constant := (219176526824039107358814137010620376743793479) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree049.table
  base := (-450569227418955282122729810313898827549/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2835000000000000000000000000000000000000000
      center := (3735)
      previous := (0)
      next := (1935)
      square := (103262606777535039005722074090000000000000)
      linear := (-6873901586258259702975903582750000000000000)
      constant := (112245829042012108568413058742468654918237736) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52280951037804008779/25000000000000000000)
  centralHi := (209123804151216035117/100000000000000000000)
  directionLo := (211290948086160522633/100000000000000000000)
  directionHi := (105645474043080261317/50000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree050.table
  base := (-3551965689029699407215520265260519475677/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (25830)
      previous := (0)
      next := (13860)
      square := (722838247442745273040054518630000000000000)
      linear := (-48495940661992113063852306017580000000000000)
      constant := (798581260933615875445227260845180998201037987) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree050.table
  base := (-7103935215871557961820545852857396636117/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (52290)
      previous := (0)
      next := (27090)
      square := (1445676494885490546080109037260000000000000)
      linear := (-98139243621512393227768190636160000000000000)
      constant := (1635878999679696683963726051786508992751251627) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211290948086160522633/100000000000000000000)
  centralHi := (105645474043080261317/50000000000000000000)
  directionLo := (213436088850084115861/100000000000000000000)
  directionHi := (106718044425042057931/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree051.table
  base := (-3494879085487152765541729531004424905901/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (2870)
      previous := (0)
      next := (1540)
      square := (80315360826971697004450502070000000000000)
      linear := (-5492975305107245565100493385600000000000000)
      constant := (92297203703945200066543098920597048616497659) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree051.table
  base := (-279590442420667608688399319596342100771/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882000000000000000000000000000000000000000
      center := (1162)
      previous := (0)
      next := (602)
      square := (32126144330788678801780200828000000000000)
      linear := (-2223197000786870013641638469196000000000000)
      constant := (37813483382531228126760299312541065667799945) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (213436088850084115861/100000000000000000000)
  centralHi := (106718044425042057931/50000000000000000000)
  directionLo := (215559883336611177207/100000000000000000000)
  directionHi := (26944985417076397151/12500000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree052.table
  base := (-68665837265971633166383364489166586051/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1984500000000000000000000000000000000000000
      center := (2583)
      previous := (0)
      next := (1386)
      square := (72283824744274527304005451863000000000000)
      linear := (-5037761482993830710795657492322000000000000)
      constant := (86339855949348470126748837604072489099817905) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree052.table
  base := (-1373317180268178890647587657906072568729/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7938000000000000000000000000000000000000000
      center := (10458)
      previous := (0)
      next := (5418)
      square := (289135298977098109216021807452000000000000)
      linear := (-20389697289861181599995854318296000000000000)
      constant := (353724972259715236219037511804394797974714599) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (215559883336611177207/100000000000000000000)
  centralHi := (26944985417076397151/12500000000000000000)
  directionLo := (217662956390300462823/100000000000000000000)
  directionHi := (27207869548787557853/12500000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree053.table
  base := (-6734408713701020343746251838610896934207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (51660)
      previous := (0)
      next := (27720)
      square := (1445676494885490546080109037260000000000000)
      linear := (-102636903827822808260017418752080000000000000)
      constant := (1793504876160738926704807287586573350068132417) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree053.table
  base := (-6734410349866148805728325934426931187527/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (52290)
      previous := (0)
      next := (27090)
      square := (1445676494885490546080109037260000000000000)
      linear := (-103853107863202665386084812069140000000000000)
      constant := (1836933324506578698915563206268234510116705337) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (217662956390300462823/100000000000000000000)
  centralHi := (27207869548787557853/12500000000000000000)
  directionLo := (219745902953930545189/100000000000000000000)
  directionHi := (21974590295393054519/10000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree054.table
  base := (-1648308424509095846817616309489427148809/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1102500000000000000000000000000000000000000
      center := (1435)
      previous := (0)
      next := (770)
      square := (40157680413485848502225251035000000000000)
      linear := (-2903293833215805619558935768270000000000000)
      constant := (51707581554079400342162086336635162627375231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree054.table
  base := (-3296617464283195781056730356889860701933/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (2905)
      previous := (0)
      next := (1505)
      square := (80315360826971697004450502070000000000000)
      linear := (-5875429404283301265121686252600000000000000)
      constant := (105918452209122986561251197411381571430447547) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (219745902953930545189/100000000000000000000)
  centralHi := (21974590295393054519/10000000000000000000)
  directionLo := (55452322508569625919/25000000000000000000)
  directionHi := (221809290034278503677/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree055.table
  base := (-3221529583286321815902745392478821470761/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (25830)
      previous := (0)
      next := (13860)
      square := (722838247442745273040054518630000000000000)
      linear := (-53200126081857598174112978281680000000000000)
      constant := (965350648206273172881202293532301557582549591) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree055.table
  base := (-6443060091715911591182913460670394551969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (52290)
      previous := (0)
      next := (27090)
      square := (1445676494885490546080109037260000000000000)
      linear := (-107662350690996180158295893024460000000000000)
      constant := (1977421305268466706135836793795374204023235039) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55452322508569625919/25000000000000000000)
  centralHi := (221809290034278503677/100000000000000000000)
  directionLo := (2798170731309985587/1250000000000000000)
  directionHi := (223853658504798846961/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree056.table
  base := (-3141942772774824838482147080660592954623/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2835000000000000000000000000000000000000000
      center := (3690)
      previous := (0)
      next := (1980)
      square := (103262606777535039005722074090000000000000)
      linear := (-7734423309404385028023587533500000000000000)
      constant := (142942139704718340567617990259505443794728759) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree056.table
  base := (-1570971560216664252071748831295251296553/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2835000000000000000000000000000000000000000
      center := (3735)
      previous := (0)
      next := (1935)
      square := (103262606777535039005722074090000000000000)
      linear := (-7826212293206638396028673821580000000000000)
      constant := (146400058530398418638977395891791185029708898) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2798170731309985587/1250000000000000000)
  centralHi := (223853658504798846961/100000000000000000000)
  directionLo := (45175904952288679601/20000000000000000000)
  directionHi := (112939762380721699003/50000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree057.table
  base := (-6115713213944521356783527340634458055531/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5740)
      previous := (0)
      next := (3080)
      square := (160630721653943394008901004140000000000000)
      linear := (-12240400055511953826270499374960000000000000)
      constant := (230326545867025498916587274015680203997510829) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree057.table
  base := (-3057856868181704649383886083106538816323/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (2905)
      previous := (0)
      next := (1505)
      square := (80315360826971697004450502070000000000000)
      linear := (-6192866306599427496139276332210000000000000)
      constant := (117948371155852154712041063337777516382001557) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45175904952288679601/20000000000000000000)
  centralHi := (112939762380721699003/50000000000000000000)
  directionLo := (11394369112299278721/5000000000000000000)
  directionHi := (227887382245985574421/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree058.table
  base := (-5938542513541212146379915020265960144171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (51660)
      previous := (0)
      next := (27720)
      square := (1445676494885490546080109037260000000000000)
      linear := (-112045274667553778480538763280280000000000000)
      constant := (2145948165867524001327567114264884404187785301) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree058.table
  base := (-296927145296738341257097200604137972803/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3969000000000000000000000000000000000000000
      center := (5229)
      previous := (0)
      next := (2709)
      square := (144567649488549054608010903726000000000000)
      linear := (-11337621493268645231661251445744000000000000)
      constant := (219783088810699467084817480416774352771889786) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11394369112299278721/5000000000000000000)
  centralHi := (227887382245985574421/100000000000000000000)
  directionLo := (229877702849581218817/100000000000000000000)
  directionHi := (114938851424790609409/50000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree059.table
  base := (-1438093439120366005380753997616054895233/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9922500000000000000000000000000000000000000
      center := (12915)
      previous := (0)
      next := (6930)
      square := (361419123721372636520027259315000000000000)
      linear := (-28481737208874993131160758046480000000000000)
      constant := (555054428455012431819916857291466878120820223) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree059.table
  base := (-1438093512781163473205817888482489310321/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (26145)
      previous := (0)
      next := (13545)
      square := (722838247442745273040054518630000000000000)
      linear := (-57640418173291604851359027467550000000000000)
      constant := (1136940720066858841735901659282593499854671902) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229877702849581218817/100000000000000000000)
  centralHi := (114938851424790609409/50000000000000000000)
  directionLo := (231850938207876961851/100000000000000000000)
  directionHi := (57962734551969240463/25000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree060.table
  base := (-5557207230947345622963248038442245000037/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5740)
      previous := (0)
      next := (3080)
      square := (160630721653943394008901004140000000000000)
      linear := (-12867624778160685174305255676840000000000000)
      constant := (255083061724112448630049778071846969954983683) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree060.table
  base := (-555720745212784695512293253808442207433/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 441000000000000000000000000000000000000000
      center := (581)
      previous := (0)
      next := (301)
      square := (16063072165394339400890100414000000000000)
      linear := (-1302060641783110745431373282364000000000000)
      constant := (26124692619704608388271473542190476986522047) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231850938207876961851/100000000000000000000)
  centralHi := (57962734551969240463/25000000000000000000)
  directionLo := (2922594011221698527/1250000000000000000)
  directionHi := (233807520897735882161/100000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree061.table
  base := (-1070608641091316719140993622731625256481/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7938000000000000000000000000000000000000000
      center := (10332)
      previous := (0)
      next := (5544)
      square := (289135298977098109216021807452000000000000)
      linear := (-23538059434278472122570313999440000000000000)
      constant := (474507537978532815089177308394950179357026911) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree061.table
  base := (-2676521685722404475832243050763978595921/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (26145)
      previous := (0)
      next := (13545)
      square := (722838247442745273040054518630000000000000)
      linear := (-59545039587188362237464567945210000000000000)
      constant := (1214926786992110773929348399324465268952789551) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2922594011221698527/1250000000000000000)
  centralHi := (233807520897735882161/100000000000000000000)
  directionLo := (117873932772281782887/50000000000000000000)
  directionHi := (9429914621782542631/4000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree062.table
  base := (-5139881932126901700162883874304347042499/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (51660)
      previous := (0)
      next := (27720)
      square := (1445676494885490546080109037260000000000000)
      linear := (-119571971339338554656955838902840000000000000)
      constant := (2450588115946350595000897072454886046588321469) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree062.table
  base := (-5139882056661969767715884549140083586031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (52290)
      previous := (0)
      next := (27090)
      square := (1445676494885490546080109037260000000000000)
      linear := (-120994700588273481861034676368080000000000000)
      constant := (2509775153783467521999967355422483008247042961) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117873932772281782887/50000000000000000000)
  centralHi := (9429914621782542631/4000000000000000000)
  directionLo := (118836184924132053371/50000000000000000000)
  directionHi := (237672369848264106743/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree063.table
  base := (-1229430912293279782859502625217553384579/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 157500000000000000000000000000000000000000
      center := (205)
      previous := (0)
      next := (110)
      square := (5736811487640835500317893005000000000000)
      linear := (-481958910743193447226428999240000000000000)
      constant := (10039281082272210233929062162046294136771523) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree063.table
  base := (-9604929184732798941208716408476628813/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 315000000000000000000000000000000000000000
      center := (415)
      previous := (0)
      next := (215)
      square := (11473622975281671000635786010000000000000)
      linear := (-975391444461668565453493784490000000000000)
      constant := (20563389478089017004151195422376588930503936) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118836184924132053371/50000000000000000000)
  centralHi := (237672369848264106743/100000000000000000000)
  directionLo := (239581415535016950351/100000000000000000000)
  directionHi := (14973838470938559397/6250000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree064.table
  base := (-117164214570808936281524970270738731737/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1984500000000000000000000000000000000000000
      center := (2583)
      previous := (0)
      next := (1386)
      square := (72283824744274527304005451863000000000000)
      linear := (-6166765983761547137258218835706000000000000)
      constant := (130523491967673404590752868301126875947471694) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree064.table
  base := (-937313730575789583310820747206174647113/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7938000000000000000000000000000000000000000
      center := (10458)
      previous := (0)
      next := (5418)
      square := (289135298977098109216021807452000000000000)
      linear := (-24960788683213399326649151464680000000000000)
      constant := (534697866892743863518501686339010692825608503) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239581415535016950351/100000000000000000000)
  centralHi := (14973838470938559397/6250000000000000000)
  directionLo := (241475369241326311581/100000000000000000000)
  directionHi := (120737684620663155791/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree065.table
  base := (-1111604237215524895981302800020155773249/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9922500000000000000000000000000000000000000
      center := (12915)
      previous := (0)
      next := (6930)
      square := (361419123721372636520027259315000000000000)
      linear := (-31304248460794284197317161404940000000000000)
      constant := (673075283738155620967294455166545001735974719) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree065.table
  base := (-88928340027521534583022180560035946997/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3969000000000000000000000000000000000000000
      center := (5229)
      previous := (0)
      next := (2709)
      square := (144567649488549054608010903726000000000000)
      linear := (-12670856482996375401935129780106000000000000)
      constant := (275728193360829830978041232870443586631844535) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (241475369241326311581/100000000000000000000)
  centralHi := (120737684620663155791/50000000000000000000)
  directionLo := (24335458333614204061/10000000000000000000)
  directionHi := (243354583336142040611/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree066.table
  base := (-4197268953718400896257580360617529029887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5740)
      previous := (0)
      next := (3080)
      square := (160630721653943394008901004140000000000000)
      linear := (-14122074223458147870374768280600000000000000)
      constant := (308376968745626230151283214768007669697819833) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree066.table
  base := (-4197268993078907907142733341298519011867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5810)
      previous := (0)
      next := (3010)
      square := (160630721653943394008901004140000000000000)
      linear := (-14290354027095612378384093142080000000000000)
      constant := (315818318984365659957967326009467353115766653) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24335458333614204061/10000000000000000000)
  centralHi := (243354583336142040611/100000000000000000000)
  directionLo := (61304849171568251939/25000000000000000000)
  directionHi := (245219396686273007757/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree067.table
  base := (-787824959098768910445521617360050991921/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7938000000000000000000000000000000000000000
      center := (10332)
      previous := (0)
      next := (5544)
      square := (289135298977098109216021807452000000000000)
      linear := (-25796068435813904975495436686208000000000000)
      constant := (571948917968255878342875150027677957613065551) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree067.table
  base := (-492390603123597180085482567739854258439/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (26145)
      previous := (0)
      next := (13545)
      square := (722838247442745273040054518630000000000000)
      linear := (-65258903828878634395781189378190000000000000)
      constant := (1464369072717399452285732256886609573793022436) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61304849171568251939/25000000000000000000)
  centralHi := (245219396686273007757/100000000000000000000)
  directionLo := (247070135369801708857/100000000000000000000)
  directionHi := (123535067684900854429/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree068.table
  base := (-917996166168581649188018353893674390791/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9922500000000000000000000000000000000000000
      center := (12915)
      previous := (0)
      next := (6930)
      square := (361419123721372636520027259315000000000000)
      linear := (-32715504086753929730395363084170000000000000)
      constant := (736339186897128480881345894086876006342950521) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree068.table
  base := (-917996171692891873063608550013105684227/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (26145)
      previous := (0)
      next := (13545)
      square := (722838247442745273040054518630000000000000)
      linear := (-66211214535827013088833959617020000000000000)
      constant := (1508200878291019159163402585869195967078606074) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (247070135369801708857/100000000000000000000)
  centralHi := (123535067684900854429/50000000000000000000)
  directionLo := (248907113341753576769/100000000000000000000)
  directionHi := (24890711334175357677/10000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree069.table
  base := (-3395848744758576084336321783513940632313/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5740)
      previous := (0)
      next := (3080)
      square := (160630721653943394008901004140000000000000)
      linear := (-14749298946106879218409524582480000000000000)
      constant := (336914354580448134575248966166850352181149967) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree069.table
  base := (-3395848761310002317143750487897764089779/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5810)
      previous := (0)
      next := (3010)
      square := (160630721653943394008901004140000000000000)
      linear := (-14925227831727864840419273301300000000000000)
      constant := (345039522619460849813164965719252086036407461) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (248907113341753576769/100000000000000000000)
  centralHi := (24890711334175357677/10000000000000000000)
  directionLo := (250730633055869305041/100000000000000000000)
  directionHi := (125365316527934652521/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree070.table
  base := (-1555358606386537830923690086454595232431/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2835000000000000000000000000000000000000000
      center := (3690)
      previous := (0)
      next := (1980)
      square := (103262606777535039005722074090000000000000)
      linear := (-9616097477350579072127856439140000000000000)
      constant := (222882994288944224646037991250580244503211623) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree070.table
  base := (-3110717225167952997228508970176941827327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (7470)
      previous := (0)
      next := (3870)
      square := (206525213555070078011444148180000000000000)
      linear := (-19461667414206791564268428598480000000000000)
      constant := (456514283673334984317504921772209673983905591) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (250730633055869305041/100000000000000000000)
  centralHi := (125365316527934652521/50000000000000000000)
  directionLo := (252540986045967202841/100000000000000000000)
  directionHi := (126270493022983601421/50000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree071.table
  base := (-2816590239706722987056124133619336487943/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (51660)
      previous := (0)
      next := (27720)
      square := (1445676494885490546080109037260000000000000)
      linear := (-136507038850854301053894259053600000000000000)
      constant := (3209754933373416790323564517309524853479354233) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree071.table
  base := (-2816590248987002767951185605381714114551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (52290)
      previous := (0)
      next := (27090)
      square := (1445676494885490546080109037260000000000000)
      linear := (-138136293313344298335984540667020000000000000)
      constant := (3287134602319353600177483267455734976679347081) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (252540986045967202841/100000000000000000000)
  centralHi := (126270493022983601421/50000000000000000000)
  directionLo := (508676906940119787/200000000000000000)
  directionHi := (254338453470059893501/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree072.table
  base := (-2513467990883404856449737047552319763433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5740)
      previous := (0)
      next := (3080)
      square := (160630721653943394008901004140000000000000)
      linear := (-15376523668755610566444280884360000000000000)
      constant := (366712025616939515591008998229229426984326047) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree072.table
  base := (-2513467997830358665119344815869666150009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5810)
      previous := (0)
      next := (3010)
      square := (160630721653943394008901004140000000000000)
      linear := (-15560101636360117302454453460520000000000000)
      constant := (375551061415337545495356768159081477227846031) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (508676906940119787/200000000000000000)
  centralHi := (254338453470059893501/100000000000000000000)
  directionLo := (256123306620100939033/100000000000000000000)
  directionHi := (128061653310050469517/50000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree073.table
  base := (-2201350626286083029781666067958610921513/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (51660)
      previous := (0)
      next := (27720)
      square := (1445676494885490546080109037260000000000000)
      linear := (-140270387186746689142102796864880000000000000)
      constant := (3392321810947363319806619846017492273252514903) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree073.table
  base := (-1100675315742690067618559690299266292149/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (26145)
      previous := (0)
      next := (13545)
      square := (722838247442745273040054518630000000000000)
      linear := (-70972768070568906554097810811170000000000000)
      constant := (1737037418167600894210771243666889712086460619) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (256123306620100939033/100000000000000000000)
  centralHi := (128061653310050469517/50000000000000000000)
  directionLo := (51579161479995644273/20000000000000000000)
  directionHi := (128947903699989110683/50000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree074.table
  base := (-1880238300842598615133706998546900312721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (51660)
      previous := (0)
      next := (27720)
      square := (1445676494885490546080109037260000000000000)
      linear := (-142152061354692883186207065770520000000000000)
      constant := (3485495673943231227428204455627887352658810351) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree074.table
  base := (-376047660946635134344742319729072779669/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7938000000000000000000000000000000000000000
      center := (10458)
      previous := (0)
      next := (5418)
      square := (289135298977098109216021807452000000000000)
      linear := (-28770031511006914098860232420000000000000000)
      constant := (713896090499303803491419435047367310137493739) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (51579161479995644273/20000000000000000000)
  centralHi := (128947903699989110683/50000000000000000000)
  directionLo := (259656208774138658269/100000000000000000000)
  directionHi := (25965620877413865827/10000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree075.table
  base := (-48441598896277614450303007152527591103/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1102500000000000000000000000000000000000000
      center := (1435)
      previous := (0)
      next := (770)
      square := (40157680413485848502225251035000000000000)
      linear := (-4000937097851085478619759296560000000000000)
      constant := (99442494970672266691049069062890882658588616) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree075.table
  base := (-1550131167591632667514467602338770023393/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5810)
      previous := (0)
      next := (3010)
      square := (160630721653943394008901004140000000000000)
      linear := (-16194975440992369764489633619740000000000000)
      constant := (407352933402952066833590509815743602419683687) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259656208774138658269/100000000000000000000)
  centralHi := (25965620877413865827/10000000000000000000)
  directionLo := (52280951037804008779/20000000000000000000)
  directionHi := (32675594398627505487/12500000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree076.table
  base := (-30275734083984933222578238595657649739/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1984500000000000000000000000000000000000000
      center := (2583)
      previous := (0)
      next := (1386)
      square := (72283824744274527304005451863000000000000)
      linear := (-7295770484529263563720780179090000000000000)
      constant := (183781212268627645788000402657795669576371818) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree076.table
  base := (-1211029365536700701558126754854992979471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (52290)
      previous := (0)
      next := (27090)
      square := (1445676494885490546080109037260000000000000)
      linear := (-147659400382828085266512243055320000000000000)
      constant := (3764162680147956496678347180115900532864479601) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52280951037804008779/20000000000000000000)
  centralHi := (32675594398627505487/12500000000000000000)
  directionLo := (65785420742319457321/25000000000000000000)
  directionHi := (52628336593855565857/20000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree077.table
  base := (-215733259519302931912962626545886877197/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1417500000000000000000000000000000000000000
      center := (1845)
      previous := (0)
      next := (990)
      square := (51631303388767519502861037045000000000000)
      linear := (-5278467280661838047089995445980000000000000)
      constant := (134734962595280930530652926971523482140629301) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree077.table
  base := (-34517321588224095526712849220599600057/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1134000000000000000000000000000000000000000
      center := (1494)
      previous := (0)
      next := (774)
      square := (41305042711014015602288829636000000000000)
      linear := (-4273257765620709790074793815228000000000000)
      constant := (110383979728585973326542460827416600133838405) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65785420742319457321/25000000000000000000)
  centralHi := (52628336593855565857/20000000000000000000)
  directionLo := (4138550323291018383/1562500000000000000)
  directionHi := (264867220690625176513/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree078.table
  base := (-126460581466783784912849778691050056311/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1102500000000000000000000000000000000000000
      center := (1435)
      previous := (0)
      next := (770)
      square := (40157680413485848502225251035000000000000)
      linear := (-4157743278513268315628448372030000000000000)
      constant := (107522053896840494502925469281917246925166849) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree078.table
  base := (-505842327084794105505148498559426581329/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5810)
      previous := (0)
      next := (3010)
      square := (160630721653943394008901004140000000000000)
      linear := (-16829849245624622226524813778960000000000000)
      constant := (440445136793391896154367561613035292877633911) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4138550323291018383/1562500000000000000)
  centralHi := (264867220690625176513/100000000000000000000)
  directionLo := (66645397382737899027/25000000000000000000)
  directionHi := (266581589530951596109/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree079.table
  base := (-139757359774485770538248863040127268197/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (51660)
      previous := (0)
      next := (27720)
      square := (1445676494885490546080109037260000000000000)
      linear := (-151560432194423853406728410298720000000000000)
      constant := (3970269207699671289542941706699413734872526107) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree079.table
  base := (-139757360684864319075176326047890685939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (52290)
      previous := (0)
      next := (27090)
      square := (1445676494885490546080109037260000000000000)
      linear := (-153373264624518357424828864488300000000000000)
      constant := (4065863501540091467939723342821650921867508109) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66645397382737899027/25000000000000000000)
  centralHi := (266581589530951596109/100000000000000000000)
  directionLo := (268285003601247122797/100000000000000000000)
  directionHi := (134142501800623561399/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree080.table
  base := (94128692390580133079718583356339229/4000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1984500000000000000000000000000000000000000
      center := (2583)
      previous := (0)
      next := (1386)
      square := (72283824744274527304005451863000000000000)
      linear := (-7672105318118502372541633960218000000000000)
      constant := (203550237719760766292532990755447663799987625) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree080.table
  base := (117660865147958475300234404788130558249/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (26145)
      previous := (0)
      next := (13545)
      square := (722838247442745273040054518630000000000000)
      linear := (-77638943019207557405467202482980000000000000)
      constant := (2084505550593207170184390829191804090185690281) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (268285003601247122797/100000000000000000000)
  centralHi := (134142501800623561399/50000000000000000000)
  directionLo := (269977670257733725909/100000000000000000000)
  directionHi := (26997767025773372591/10000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree081.table
  base := (61939482082667853614909370543942630749/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 441000000000000000000000000000000000000000
      center := (574)
      previous := (0)
      next := (308)
      square := (16063072165394339400890100414000000000000)
      linear := (-1725819783670180461054854979000000000000000)
      constant := (46366673109717180681405265813763878700160309) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree081.table
  base := (309697410159019770351122166805029530309/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (2905)
      previous := (0)
      next := (1505)
      square := (80315360826971697004450502070000000000000)
      linear := (-8732361525128437344279996969090000000000000)
      constant := (237413834976734964824458457595788518022866269) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269977670257733725909/100000000000000000000)
  centralHi := (26997767025773372591/10000000000000000000)
  directionLo := (271659790396492100529/100000000000000000000)
  directionHi := (27165979039649210053/10000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree082.table
  base := (1012461787736200946152785503538182818127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (51660)
      previous := (0)
      next := (27720)
      square := (1445676494885490546080109037260000000000000)
      linear := (-157205454698262435539041217015640000000000000)
      constant := (4276256683653287344330454010669143047605146063) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree082.table
  base := (1012461787356095283715465933325179492433/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (52290)
      previous := (0)
      next := (27090)
      square := (1445676494885490546080109037260000000000000)
      linear := (-159087128866208629583145485921280000000000000)
      constant := (4379177286240217702337269295806187637405466577) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (271659790396492100529/100000000000000000000)
  centralHi := (27165979039649210053/10000000000000000000)
  directionLo := (273331558731768918493/100000000000000000000)
  directionHi := (136665779365884459247/50000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree083.table
  base := (1414522513046144475857958608072681381721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (51660)
      previous := (0)
      next := (27720)
      square := (1445676494885490546080109037260000000000000)
      linear := (-159087128866208629583145485921280000000000000)
      constant := (4380773065260481507580882849232260472404050649) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree083.table
  base := (88407657047633344828278186245068294197/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (26145)
      previous := (0)
      next := (13545)
      square := (722838247442745273040054518630000000000000)
      linear := (-80495875140052693484625513199470000000000000)
      constant := (2243097935346232815340408061637940908477343144) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273331558731768918493/100000000000000000000)
  centralHi := (136665779365884459247/50000000000000000000)
  directionLo := (137496582029527975583/50000000000000000000)
  directionHi := (274993164059055951167/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree084.table
  base := (1825576881348476694247438491535727473611/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (820)
      previous := (0)
      next := (440)
      square := (22947245950563342001271572020000000000000)
      linear := (-2555060365621505136940472298840000000000000)
      constant := (71215074987905940799350051956006750830837493) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree084.table
  base := (912788440568148584095097511597695717991/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 315000000000000000000000000000000000000000
      center := (415)
      previous := (0)
      next := (215)
      square := (11473622975281671000635786010000000000000)
      linear := (-1292828346777794796471083864100000000000000)
      constant := (36464323670475802532917996146590654830233433) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137496582029527975583/50000000000000000000)
  centralHi := (274993164059055951167/100000000000000000000)
  directionLo := (11065791580157889943/4000000000000000000)
  directionHi := (4322574835999175759/1562500000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree085.table
  base := (449124956072523722605181019356402290711/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7938000000000000000000000000000000000000000
      center := (10332)
      previous := (0)
      next := (5544)
      square := (289135298977098109216021807452000000000000)
      linear := (-32570095440420203534270804746512000000000000)
      constant := (918717332028084802932084231470165560691831959) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree085.table
  base := (561406195051031323196371923785353093373/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (26145)
      previous := (0)
      next := (13545)
      square := (722838247442745273040054518630000000000000)
      linear := (-82400496553949450870731053677130000000000000)
      constant := (2352052010578528416126053333719595632855194874) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (11065791580157889943/4000000000000000000)
  centralHi := (4322574835999175759/1562500000000000000)
  directionLo := (69571653189425730081/25000000000000000000)
  directionHi := (11131464510308116813/4000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree086.table
  base := (1337333050409187311842893734547003961163/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (25830)
      previous := (0)
      next := (13860)
      square := (722838247442745273040054518630000000000000)
      linear := (-82366075685023605857729146319100000000000000)
      constant := (2350941936266918667057409976240097058721855947) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree086.table
  base := (534933220139999978661743463119478741629/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7938000000000000000000000000000000000000000
      center := (10458)
      previous := (0)
      next := (5418)
      square := (289135298977098109216021807452000000000000)
      linear := (-33341122904359131825513529566384000000000000)
      constant := (962998717258021506432228950684725211125525501) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (69571653189425730081/25000000000000000000)
  centralHi := (11131464510308116813/4000000000000000000)
  directionLo := (27991880630037725601/10000000000000000000)
  directionHi := (279918806300377256011/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree087.table
  base := (1556350368172343055083903710691478892767/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (2870)
      previous := (0)
      next := (1540)
      square := (80315360826971697004450502070000000000000)
      linear := (-9256323640999633653309031196880000000000000)
      constant := (267302297833118194281950576860664942191710247) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree087.table
  base := (3112700736256286778214515935665322681979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5810)
      previous := (0)
      next := (3010)
      square := (160630721653943394008901004140000000000000)
      linear := (-18734470659521379612630354256620000000000000)
      constant := (547463719717436675418726467448283407302752739) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27991880630037725601/10000000000000000000)
  centralHi := (279918806300377256011/100000000000000000000)
  directionLo := (8798173050384508541/3125000000000000000)
  directionHi := (281541537612304273313/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree088.table
  base := (3559728583363782999235475390067576985651/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (51660)
      previous := (0)
      next := (27720)
      square := (1445676494885490546080109037260000000000000)
      linear := (-168495499705939599803666830449480000000000000)
      constant := (4922259125116194334120616823308298213056048819) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree088.table
  base := (3559728583297777176886314733447999018087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (52290)
      previous := (0)
      next := (27090)
      square := (1445676494885490546080109037260000000000000)
      linear := (-170514857349589173899778728787240000000000000)
      constant := (5040643694246434468463709866617855108102787303) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8798173050384508541/3125000000000000000)
  centralHi := (281541537612304273313/100000000000000000000)
  directionLo := (283154969374674690409/100000000000000000000)
  directionHi := (28315496937467469041/10000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree089.table
  base := (4015749540990361251239463519865638118029/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (51660)
      previous := (0)
      next := (27720)
      square := (1445676494885490546080109037260000000000000)
      linear := (-170377173873885793847771099355120000000000000)
      constant := (5034337164493624073517971089671566717690457101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree089.table
  base := (803149908188216491032924333851887614251/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7938000000000000000000000000000000000000000
      center := (10458)
      previous := (0)
      next := (5418)
      square := (289135298977098109216021807452000000000000)
      linear := (-34483895752697186257176853852980000000000000)
      constant := (1031080847251642906351536141653605141940962219) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (283154969374674690409/100000000000000000000)
  centralHi := (28315496937467469041/10000000000000000000)
  directionLo := (17797453728742765659/6250000000000000000)
  directionHi := (56951851931976850109/20000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree090.table
  base := (1120190877733864360927804768078261505333/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1102500000000000000000000000000000000000000
      center := (1435)
      previous := (0)
      next := (770)
      square := (40157680413485848502225251035000000000000)
      linear := (-4784968001161999663663204673910000000000000)
      constant := (142990985520508550540094319354522513323851853) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree090.table
  base := (1120190877724667835550741952222088047947/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (2905)
      previous := (0)
      next := (1505)
      square := (80315360826971697004450502070000000000000)
      linear := (-9684672232076816037332767207920000000000000)
      constant := (292858616839009280946470060932509881658289254) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17797453728742765659/6250000000000000000)
  centralHi := (56951851931976850109/20000000000000000000)
  directionLo := (286354562112283801969/100000000000000000000)
  directionHi := (28635456211228380197/10000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree091.table
  base := (4954770397414726694276174894937823843193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (7380)
      previous := (0)
      next := (3960)
      square := (206525213555070078011444148180000000000000)
      linear := (-24877217458539740276568519595200000000000000)
      constant := (751753438210011072436963626793409746119090431) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree091.table
  base := (4954770397387269605661415986056359706593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (7470)
      previous := (0)
      next := (3870)
      square := (206525213555070078011444148180000000000000)
      linear := (-25175531655897063722585050031460000000000000)
      constant := (769828042056875461267413403079478955953638231) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (286354562112283801969/100000000000000000000)
  centralHi := (28635456211228380197/10000000000000000000)
  directionLo := (287941026119916128041/100000000000000000000)
  directionHi := (143970513059958064021/50000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree092.table
  base := (339860631691303693624770835752973101709/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9922500000000000000000000000000000000000000
      center := (12915)
      previous := (0)
      next := (6930)
      square := (361419123721372636520027259315000000000000)
      linear := (-44005549094431093995020976518010000000000000)
      constant := (1344533232579589570837830462377014200962732084) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree092.table
  base := (2718885053520183806737059198582478642049/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (26145)
      previous := (0)
      next := (13545)
      square := (722838247442745273040054518630000000000000)
      linear := (-89066671502588101722100445348940000000000000)
      constant := (2753713904887763185267154766324533857730292481) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287941026119916128041/100000000000000000000)
  centralHi := (143970513059958064021/50000000000000000000)
  directionLo := (289518796977782846547/100000000000000000000)
  directionHi := (72379699244445711637/25000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree093.table
  base := (5929762548839894029998124362617985719417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5740)
      previous := (0)
      next := (3080)
      square := (160630721653943394008901004140000000000000)
      linear := (-19767096727296730002687574997520000000000000)
      constant := (610583562991315150955666853637294531702262897) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree093.table
  base := (5929762548824602825027280010212501037039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5810)
      previous := (0)
      next := (3010)
      square := (160630721653943394008901004140000000000000)
      linear := (-20004218268785884536700714575060000000000000)
      constant := (625261072097005562900001341953478712957334199) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (289518796977782846547/100000000000000000000)
  centralHi := (72379699244445711637/25000000000000000000)
  directionLo := (291088016043146410291/100000000000000000000)
  directionHi := (72772004010786602573/25000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree094.table
  base := (1607686908492803036250925770141904576137/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9922500000000000000000000000000000000000000
      center := (12915)
      previous := (0)
      next := (6930)
      square := (361419123721372636520027259315000000000000)
      linear := (-44946386178404191017073110970830000000000000)
      constant := (1403407869232035363656594280320173219262687753) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree094.table
  base := (321537381697990140351333264970009095613/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3969000000000000000000000000000000000000000
      center := (5229)
      previous := (0)
      next := (2709)
      square := (144567649488549054608010903726000000000000)
      linear := (-18194258583296971821641197165320000000000000)
      constant := (574856181133833081118125663555117932200975994) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291088016043146410291/100000000000000000000)
  centralHi := (72772004010786602573/25000000000000000000)
  directionLo := (146324410441668516877/50000000000000000000)
  directionHi := (58529764176667406751/20000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree095.table
  base := (1735181318962750621540991153035990432331/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9922500000000000000000000000000000000000000
      center := (12915)
      previous := (0)
      next := (6930)
      square := (361419123721372636520027259315000000000000)
      linear := (-45416804720390739528099178197240000000000000)
      constant := (1433317789998385761434928516935124846025921739) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree095.table
  base := (3470362637921245252130696608501462519639/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (26145)
      previous := (0)
      next := (13545)
      square := (722838247442745273040054518630000000000000)
      linear := (-91923603623433237801258756065430000000000000)
      constant := (2935532148413819702672955609840129804740447191) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (146324410441668516877/50000000000000000000)
  centralHi := (58529764176667406751/20000000000000000000)
  directionLo := (294201345416501965361/100000000000000000000)
  directionHi := (147100672708250982681/50000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree096.table
  base := (298387815599160695831248063467288225713/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882000000000000000000000000000000000000000
      center := (1148)
      previous := (0)
      next := (616)
      square := (32126144330788678801780200828000000000000)
      linear := (-4078864289989092270144466259880000000000000)
      constant := (130092691461836881088613562701353370537697165) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree096.table
  base := (7459695389972667691820582883689044568973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5810)
      previous := (0)
      next := (3010)
      square := (160630721653943394008901004140000000000000)
      linear := (-20639092073418136998735894734280000000000000)
      constant := (666095233889510595071033838195386868654917093) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (294201345416501965361/100000000000000000000)
  centralHi := (147100672708250982681/50000000000000000000)
  directionLo := (18484107502856541973/6250000000000000000)
  directionHi := (295745720045704671569/100000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree097.table
  base := (7987657893888441354263121380471256193233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (51660)
      previous := (0)
      next := (27720)
      square := (1445676494885490546080109037260000000000000)
      linear := (-185430567217455346200605250600240000000000000)
      constant := (5976331343968180473572804073318390415830941777) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree097.table
  base := (3993828946941852578396835443648682321987/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (26145)
      previous := (0)
      next := (13545)
      square := (722838247442745273040054518630000000000000)
      linear := (-93828225037329995187364296543090000000000000)
      constant := (3059970117772444305357697290801489120135966403) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18484107502856541973/6250000000000000000)
  centralHi := (295745720045704671569/100000000000000000000)
  directionLo := (29728207178675397213/10000000000000000000)
  directionHi := (297282071786753972131/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree098.table
  base := (8524612707078711806692521184828119546097/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (7380)
      previous := (0)
      next := (3960)
      square := (206525213555070078011444148180000000000000)
      linear := (-26758891626485934320672788500840000000000000)
      constant := (871393120604371255244975563580757543782636999) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree098.table
  base := (340984508283007179276199690878678845973/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1134000000000000000000000000000000000000000
      center := (1494)
      previous := (0)
      next := (774)
      square := (41305042711014015602288829636000000000000)
      linear := (-5416030613958764221738118101824000000000000)
      constant := (178466105375028942572314691971541054528333455) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29728207178675397213/10000000000000000000)
  centralHi := (297282071786753972131/100000000000000000000)
  directionLo := (59762104878023552441/20000000000000000000)
  directionHi := (149405262195058881103/50000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree099.table
  base := (2267639937737785183441438058089400955683/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1102500000000000000000000000000000000000000
      center := (1435)
      previous := (0)
      next := (770)
      square := (40157680413485848502225251035000000000000)
      linear := (-5255386543148548174689271900320000000000000)
      constant := (172900906007165455435140798745662425821456203) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree099.table
  base := (9070559750948506544974170658637988505721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5810)
      previous := (0)
      next := (3010)
      square := (160630721653943394008901004140000000000000)
      linear := (-21273965878050389460771074893500000000000000)
      constant := (708219718048556745911692171345874352931022961) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (59762104878023552441/20000000000000000000)
  centralHi := (149405262195058881103/50000000000000000000)
  directionLo := (75082799614313123181/25000000000000000000)
  directionHi := (12013247938290099709/4000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree100.table
  base := (4812749474373597695078537521175811691401/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (25830)
      previous := (0)
      next := (13860)
      square := (722838247442745273040054518630000000000000)
      linear := (-95537794860646964166459028658580000000000000)
      constant := (3175186829872799341978662821327546796603170569) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree100.table
  base := (9625498948745231172928229004589381852711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (52290)
      previous := (0)
      next := (27090)
      square := (1445676494885490546080109037260000000000000)
      linear := (-193370314316350262533045214519160000000000000)
      constant := (6502931558173227471656113905047215256573409959) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75082799614313123181/25000000000000000000)
  centralHi := (12013247938290099709/4000000000000000000)
  directionLo := (301844211551657889477/100000000000000000000)
  directionHi := (150922105775828944739/50000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree101.table
  base := (10189430225489305427788250192513863538397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (51660)
      previous := (0)
      next := (27720)
      square := (1445676494885490546080109037260000000000000)
      linear := (-192957263889240122377022326222800000000000000)
      constant := (6477574974395939674880077076231947524383897693) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree101.table
  base := (636839389092990057988795436835444259923/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (26145)
      previous := (0)
      next := (13545)
      square := (722838247442745273040054518630000000000000)
      linear := (-97637467865123509959575377498410000000000000)
      constant := (3316587987518538759258728943087546526141075096) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (301844211551657889477/100000000000000000000)
  centralHi := (150922105775828944739/50000000000000000000)
  directionLo := (75837419576236580847/25000000000000000000)
  directionHi := (303349678304946323389/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree102.table
  base := (10762353507924071669324938712363426986213/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5740)
      previous := (0)
      next := (3080)
      square := (160630721653943394008901004140000000000000)
      linear := (-21648770895242924046791843903160000000000000)
      constant := (734004062213137403010942562688952271300919933) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree102.table
  base := (10762353507922979858730628208320642747557/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5810)
      previous := (0)
      next := (3010)
      square := (160630721653943394008901004140000000000000)
      linear := (-21908839682682641922806255052720000000000000)
      constant := (751634523637535364891117321334049403451672637) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (75837419576236580847/25000000000000000000)
  centralHi := (303349678304946323389/100000000000000000000)
  directionLo := (304847710518197663121/100000000000000000000)
  directionHi := (152423855259098831561/50000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree103.table
  base := (88627099409904368733399169373048824791/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 9922500000000000000000000000000000000000000
      center := (12915)
      previous := (0)
      next := (6930)
      square := (361419123721372636520027259315000000000000)
      linear := (-49180153056283127616307716008520000000000000)
      constant := (1683939604007093424181849768081737185139055328) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree103.table
  base := (2836067181116736327696142538581135553917/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (26145)
      previous := (0)
      next := (13545)
      square := (722838247442745273040054518630000000000000)
      linear := (-99542089279020267345680917976070000000000000)
      constant := (3448767885495667026163357773375244554026993146) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (304847710518197663121/100000000000000000000)
  centralHi := (152423855259098831561/50000000000000000000)
  directionLo := (76584604314713305727/25000000000000000000)
  directionHi := (306338417258853222909/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree104.table
  base := (11935175805153964262298236447552224944021/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (51660)
      previous := (0)
      next := (27720)
      square := (1445676494885490546080109037260000000000000)
      linear := (-198602286393078704509335132939720000000000000)
      constant := (6866740542448654227278548540860654780802819349) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree104.table
  base := (372974243911042425273508480325074256637/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (26145)
      previous := (0)
      next := (13545)
      square := (722838247442745273040054518630000000000000)
      linear := (-100494399985968646038733688214900000000000000)
      constant := (3515825574759964131253223931652243515593476048) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76584604314713305727/25000000000000000000)
  centralHi := (306338417258853222909/100000000000000000000)
  directionLo := (76955476238346612779/25000000000000000000)
  directionHi := (307821904953386451117/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree105.table
  base := (3133768670395837707203268314784442979189/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 157500000000000000000000000000000000000000
      center := (205)
      previous := (0)
      next := (110)
      square := (5736811487640835500317893005000000000000)
      linear := (-795571272067559121243807150180000000000000)
      constant := (27773741821061909738229577440006419907688907) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree105.table
  base := (6267537340791449341856373389533047933459/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 315000000000000000000000000000000000000000
      center := (415)
      previous := (0)
      next := (215)
      square := (11473622975281671000635786010000000000000)
      linear := (-1610265249093921027488673943710000000000000)
      constant := (56881403555969238263045281364253082019807917) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76955476238346612779/25000000000000000000)
  centralHi := (307821904953386451117/100000000000000000000)
  directionLo := (154649138737986593249/50000000000000000000)
  directionHi := (309298277475973186499/100000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree106.table
  base := (821497830429709905766382345020564047729/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9922500000000000000000000000000000000000000
      center := (12915)
      previous := (0)
      next := (6930)
      square := (361419123721372636520027259315000000000000)
      linear := (-50591408682242773149385917687750000000000000)
      constant := (1783121401284941458186310982524386474821745604) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree106.table
  base := (821497830429688845871264158476039906659/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (26145)
      previous := (0)
      next := (13545)
      square := (722838247442745273040054518630000000000000)
      linear := (-102399021399865403424839228692560000000000000)
      constant := (3651876433161236218594319366005541219116236568) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (154649138737986593249/50000000000000000000)
  centralHi := (309298277475973186499/100000000000000000000)
  directionLo := (310767636233370546599/100000000000000000000)
  directionHi := (1553838181166852733/500000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree107.table
  base := (13761847555621788939280229529037514615617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (51660)
      previous := (0)
      next := (27720)
      square := (1445676494885490546080109037260000000000000)
      linear := (-204247308896917286641647939656640000000000000)
      constant := (7267248540885542824306973547030849895509383873) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree107.table
  base := (6880923777810768922577097713478231954009/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (26145)
      previous := (0)
      next := (13545)
      square := (722838247442745273040054518630000000000000)
      linear := (-103351332106813782117891998931390000000000000)
      constant := (3720869602035684205610934169384642602625461721) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (310767636233370546599/100000000000000000000)
  centralHi := (1553838181166852733/500000000000000000)
  directionLo := (312230080246200721871/100000000000000000000)
  directionHi := (19514380015387545117/6250000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree108.table
  base := (2877744284768436653706004393751756564043/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882000000000000000000000000000000000000000
      center := (1148)
      previous := (0)
      next := (616)
      square := (32126144330788678801780200828000000000000)
      linear := (-4580644068108077348572271301384000000000000)
      constant := (164517149908688750829769650564940524644742963) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree108.table
  base := (3597180355960499043655401168600103488171/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (2905)
      previous := (0)
      next := (1505)
      square := (80315360826971697004450502070000000000000)
      linear := (-11589293645973573423438307685580000000000000)
      constant := (421167547835826307303732600087105291276566822) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (312230080246200721871/100000000000000000000)
  centralHi := (19514380015387545117/6250000000000000000)
  directionLo := (156842853113412026337/50000000000000000000)
  directionHi := (12547428249072962107/4000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree109.table
  base := (7512293414470453626253594828183761771219/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (25830)
      previous := (0)
      next := (13860)
      square := (722838247442745273040054518630000000000000)
      linear := (-104005328616404837364928238733960000000000000)
      constant := (3770277609953838324797130764000071350469968211) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree109.table
  base := (1502458682894076785783690974939802187631/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 3969000000000000000000000000000000000000000
      center := (5229)
      previous := (0)
      next := (2709)
      square := (144567649488549054608010903726000000000000)
      linear := (-21051190704142107900799507881810000000000000)
      constant := (772158283699454574775517161417309574882707439) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156842853113412026337/50000000000000000000)
  centralHi := (12547428249072962107/4000000000000000000)
  directionLo := (157567304326987347139/50000000000000000000)
  directionHi := (315134608653974694279/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree110.table
  base := (15669443709665866099267339666795043679143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (51660)
      previous := (0)
      next := (27720)
      square := (1445676494885490546080109037260000000000000)
      linear := (-209892331400755868773960746373560000000000000)
      constant := (7679098962692481846841628009244709528362518567) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree110.table
  base := (3133888741933152450317532747449163900267/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7938000000000000000000000000000000000000000
      center := (10458)
      previous := (0)
      next := (5418)
      square := (289135298977098109216021807452000000000000)
      linear := (-42483305691063567278820123859152000000000000)
      constant := (1572688026335455102464582514956085731520159723) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (157567304326987347139/50000000000000000000)
  centralHi := (315134608653974694279/100000000000000000000)
  directionLo := (158288439922160931549/50000000000000000000)
  directionHi := (316576879844321863099/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree111.table
  base := (16323292006068774465355388079149880396157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5740)
      previous := (0)
      next := (3080)
      square := (160630721653943394008901004140000000000000)
      linear := (-23530445063189118090896112808800000000000000)
      constant := (868766997111941626061506721230445097254705237) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree111.table
  base := (1632329200606869710611543966766508090631/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 441000000000000000000000000000000000000000
      center := (581)
      previous := (0)
      next := (301)
      square := (16063072165394339400890100414000000000000)
      linear := (-2381346109657939930891179553038000000000000)
      constant := (88962086053945867699123538741609530067968271) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158288439922160931549/50000000000000000000)
  centralHi := (316576879844321863099/100000000000000000000)
  directionLo := (79503152505277511761/25000000000000000000)
  directionHi := (63602522004222009409/20000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree112.table
  base := (4246532914866727851230104906094659514721/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1417500000000000000000000000000000000000000
      center := (1845)
      previous := (0)
      next := (990)
      square := (51631303388767519502861037045000000000000)
      linear := (-7630559990594580602220331578030000000000000)
      constant := (284284544772133689046284881813755671944846807) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree112.table
  base := (16986131659466853782300123514280143293253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 5670000000000000000000000000000000000000000
      center := (7470)
      previous := (0)
      next := (3870)
      square := (206525213555070078011444148180000000000000)
      linear := (-30889395897587335880901671464440000000000000)
      constant := (1164432239470741682753017373927956841247274451) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79503152505277511761/25000000000000000000)
  centralHi := (63602522004222009409/20000000000000000000)
  directionLo := (79860471845005650117/25000000000000000000)
  directionHi := (319441887380022600469/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree113.table
  base := (17657962612406293633852982310338960200337/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (51660)
      previous := (0)
      next := (27720)
      square := (1445676494885490546080109037260000000000000)
      linear := (-215537353904594450906273553090480000000000000)
      constant := (8102291801301252963414246193421355333035137553) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree113.table
  base := (8828981306203125357907931208606342284231/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (26145)
      previous := (0)
      next := (13545)
      square := (722838247442745273040054518630000000000000)
      linear := (-109065196348504054276208620364370000000000000)
      constant := (4148376962884715859272056328516046072526112839) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79860471845005650117/25000000000000000000)
  centralHi := (319441887380022600469/100000000000000000000)
  directionLo := (8021619953810119517/2500000000000000000)
  directionHi := (320864798152404780681/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree114.table
  base := (2292348101078275494898177407818791960333/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1102500000000000000000000000000000000000000
      center := (1435)
      previous := (0)
      next := (770)
      square := (40157680413485848502225251035000000000000)
      linear := (-6039417446459462359732717277670000000000000)
      constant := (229052128245241801621374454690216174509013706) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree114.table
  base := (9169392404313085997878804819896044686241/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (2905)
      previous := (0)
      next := (1505)
      square := (80315360826971697004450502070000000000000)
      linear := (-12224167450605825885473487844800000000000000)
      constant := (469098471836363840516094970825344155706632281) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (8021619953810119517/2500000000000000000)
  centralHi := (320864798152404780681/100000000000000000000)
  directionLo := (322281426665974473401/100000000000000000000)
  directionHi := (161140713332987236701/50000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree115.table
  base := (761143927721000599545789700898097466573/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7938000000000000000000000000000000000000000
      center := (10332)
      previous := (0)
      next := (5544)
      square := (289135298977098109216021807452000000000000)
      linear := (-43860140448097367798896418180352000000000000)
      constant := (1678144339996680123808349545571382744224141185) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree115.table
  base := (9514299096512495592756869313376985917311/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (26145)
      previous := (0)
      next := (13545)
      square := (722838247442745273040054518630000000000000)
      linear := (-110969817762400811662314160842030000000000000)
      constant := (4296040688965922828090500262585080757105807359) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (322281426665974473401/100000000000000000000)
  centralHi := (161140713332987236701/50000000000000000000)
  directionLo := (64738371080628311527/20000000000000000000)
  directionHi := (80922963850785389409/25000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree116.table
  base := (19727402711627251307451003454754927356777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (51660)
      previous := (0)
      next := (27720)
      square := (1445676494885490546080109037260000000000000)
      linear := (-221182376408433033038586359807400000000000000)
      constant := (8536827050551111583509786654315282306679047913) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree116.table
  base := (19727402711627233582597789862871703639089/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (52290)
      previous := (0)
      next := (27090)
      square := (1445676494885490546080109037260000000000000)
      linear := (-223844256938698380710733862161720000000000000)
      constant := (8741680580187092640123817050158057791743544241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64738371080628311527/20000000000000000000)
  centralHi := (80922963850785389409/25000000000000000000)
  directionLo := (65019233011410007687/20000000000000000000)
  directionHi := (81274041264262509609/25000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree117.table
  base := (4087039662310367240448538811278642329963/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882000000000000000000000000000000000000000
      center := (1148)
      previous := (0)
      next := (616)
      square := (32126144330788678801780200828000000000000)
      linear := (-4956978901697316157393125082512000000000000)
      constant := (192982059296043394628850340510193881267513683) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree117.table
  base := (163481586492414584036015633435960489533/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882000000000000000000000000000000000000000
      center := (1162)
      previous := (0)
      next := (602)
      square := (32126144330788678801780200828000000000000)
      linear := (-5016641741168780846596431169764000000000000)
      constant := (197612668880231224216661901227322464397101325) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65019233011410007687/20000000000000000000)
  centralHi := (81274041264262509609/25000000000000000000)
  directionLo := (65298886917090138847/20000000000000000000)
  directionHi := (81623608646362673559/25000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree118.table
  base := (5287996235245367934346401908136092418597/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 9922500000000000000000000000000000000000000
      center := (12915)
      previous := (0)
      next := (6930)
      square := (361419123721372636520027259315000000000000)
      linear := (-56236431186081355281698724404670000000000000)
      constant := (2208204638272565321975162891853872150809411493) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree118.table
  base := (5287996235245365477797121082875782398239/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (26145)
      previous := (0)
      next := (13545)
      square := (722838247442745273040054518630000000000000)
      linear := (-113826749883245947741472471558520000000000000)
      constant := (4522374967998060075561248110784317960677221182) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (65298886917090138847/20000000000000000000)
  centralHi := (81623608646362673559/25000000000000000000)
  directionLo := (327886741262506011783/100000000000000000000)
  directionHi := (40985842657813251473/12500000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree119.table
  base := (683680079660409486180815601968313186091/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1417500000000000000000000000000000000000000
      center := (1845)
      previous := (0)
      next := (990)
      square := (51631303388767519502861037045000000000000)
      linear := (-8100978532581129113246398804440000000000000)
      constant := (320810882309088543913627811107043268612108776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree119.table
  base := (5469440637283274060584972281772181427857/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2835000000000000000000000000000000000000000
      center := (3735)
      previous := (0)
      next := (1935)
      square := (103262606777535039005722074090000000000000)
      linear := (-16397008655742046633503605971050000000000000)
      constant := (657015720653048563048324923331082153739189838) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327886741262506011783/100000000000000000000)
  centralHi := (40985842657813251473/12500000000000000000)
  directionLo := (329273160728623587103/100000000000000000000)
  directionHi := (10289786272769487097/3125000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree120.table
  base := (5653132771557356053748744183449520473303/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1102500000000000000000000000000000000000000
      center := (1435)
      previous := (0)
      next := (770)
      square := (40157680413485848502225251035000000000000)
      linear := (-6353029807783828033750095428610000000000000)
      constant := (253718086744917790279948664161301238528726623) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree120.table
  base := (4522506217245883753827774520366124429189/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 882000000000000000000000000000000000000000
      center := (1162)
      previous := (0)
      next := (602)
      square := (32126144330788678801780200828000000000000)
      linear := (-5143616502095231339003467201608000000000000)
      constant := (207844012418944847822683729394361460873272349) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (329273160728623587103/100000000000000000000)
  centralHi := (10289786272769487097/3125000000000000000)
  directionLo := (66130753407681785613/20000000000000000000)
  directionHi := (165326883519204464033/50000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree121.table
  base := (4671258100694274219805763905862104599817/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7938000000000000000000000000000000000000000
      center := (10332)
      previous := (0)
      next := (5544)
      square := (289135298977098109216021807452000000000000)
      linear := (-46118149449632800651821540867120000000000000)
      constant := (1857251561476852293978269393563538693156673673) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree121.table
  base := (11678145251735683522615883598750149780001/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (26145)
      previous := (0)
      next := (13545)
      square := (722838247442745273040054518630000000000000)
      linear := (-116683682004091083820630782275010000000000000)
      constant := (4754515672465975740152787601681686844476823969) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66130753407681785613/20000000000000000000)
  centralHi := (165326883519204464033/50000000000000000000)
  directionLo := (41503579088352959803/12500000000000000000)
  directionHi := (13281145308272947137/4000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree122.table
  base := (12054520376505788607915536011703803075989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (25830)
      previous := (0)
      next := (13860)
      square := (722838247442745273040054518630000000000000)
      linear := (-116236210708055098651605986620620000000000000)
      constant := (4719962379083118044710876707874852394408600341) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree122.table
  base := (12054520376505787099229591565524566622769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (26145)
      previous := (0)
      next := (13545)
      square := (722838247442745273040054518630000000000000)
      linear := (-117635992711039462513683552513840000000000000)
      constant := (4833186223595536834207685225218777004925770161) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (41503579088352959803/12500000000000000000)
  centralHi := (13281145308272947137/4000000000000000000)
  directionLo := (333397828753630671489/100000000000000000000)
  directionHi := (33339782875363067149/10000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree123.table
  base := (12435390893964367543779098459927935366517/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 2205000000000000000000000000000000000000000
      center := (2870)
      previous := (0)
      next := (1540)
      square := (80315360826971697004450502070000000000000)
      linear := (-13019671976892021741517569008160000000000000)
      constant := (533047331943151868849433903004118219496633997) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree123.table
  base := (24870781787928732841778464345808262965357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5810)
      previous := (0)
      next := (3010)
      square := (160630721653943394008901004140000000000000)
      linear := (-26352956315108409157052516167260000000000000)
      constant := (1091667096160406005258997918008876443967722437) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (333397828753630671489/100000000000000000000)
  centralHi := (33339782875363067149/10000000000000000000)
  directionLo := (167380712373101446427/50000000000000000000)
  directionHi := (66952284949240578571/20000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree124.table
  base := (1282075678110141798873376071241334762693/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1984500000000000000000000000000000000000000
      center := (2583)
      previous := (0)
      next := (1386)
      square := (72283824744274527304005451863000000000000)
      linear := (-11811788487600129269571025552626000000000000)
      constant := (487551972881655035240969290723612857673128517) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree124.table
  base := (6410378390550708576519736232199886873833/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (26145)
      previous := (0)
      next := (13545)
      square := (722838247442745273040054518630000000000000)
      linear := (-119540614124936219899789092991500000000000000)
      constant := (4992462799753519601322353702640882702004486354) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167380712373101446427/50000000000000000000)
  centralHi := (66952284949240578571/20000000000000000000)
  directionLo := (336119488840769366339/100000000000000000000)
  directionHi := (16805974442038468317/5000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree125.table
  base := (13210618015345624230027758359772879917521/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (25830)
      previous := (0)
      next := (13860)
      square := (722838247442745273040054518630000000000000)
      linear := (-119058721959974389717762389979080000000000000)
      constant := (4954243602978083090941328295531188560392640849) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree125.table
  base := (26421236030691247216228129284596311788271/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (52290)
      previous := (0)
      next := (27090)
      square := (1445676494885490546080109037260000000000000)
      linear := (-240985849663769197185683726460660000000000000)
      constant := (10146137649202058030428648005024937761487647599) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (336119488840769366339/100000000000000000000)
  centralHi := (16805974442038468317/5000000000000000000)
  directionLo := (168736043911083578693/50000000000000000000)
  directionHi := (337472087822167157387/100000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree126.table
  base := (27209949149105602076696466653640551872011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 630000000000000000000000000000000000000000
      center := (820)
      previous := (0)
      next := (440)
      square := (22947245950563342001271572020000000000000)
      linear := (-3809509810918967833009984902600000000000000)
      constant := (159796749520161103621100589149899354767936693) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree126.table
  base := (13604974574552800575556418343373680302769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 315000000000000000000000000000000000000000
      center := (415)
      previous := (0)
      next := (215)
      square := (11473622975281671000635786010000000000000)
      linear := (-1927702151410047258506264023320000000000000)
      constant := (81814603288515317368900038468302541859074447) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (168736043911083578693/50000000000000000000)
  centralHi := (337472087822167157387/100000000000000000000)
  directionLo := (338819287142165097007/100000000000000000000)
  directionHi := (21176205446385318563/6250000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree127.table
  base := (5601530574797888688684654836185759003419/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 7938000000000000000000000000000000000000000
      center := (10332)
      previous := (0)
      next := (5544)
      square := (289135298977098109216021807452000000000000)
      linear := (-48376158451168233504746663553888000000000000)
      constant := (2045432699780514416015692396487961277484570011) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree127.table
  base := (28007652873989442754700382326889461914143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (52290)
      previous := (0)
      next := (27090)
      square := (1445676494885490546080109037260000000000000)
      linear := (-244795092491562711957894807415980000000000000)
      constant := (10472432694787176413432884205220919274337233567) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (338819287142165097007/100000000000000000000)
  centralHi := (21176205446385318563/6250000000000000000)
  directionLo := (340161150956421451619/100000000000000000000)
  directionHi := (17008057547821072581/5000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree128.table
  base := (28814347162696633716331272469706925863543/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 39690000000000000000000000000000000000000000
      center := (51660)
      previous := (0)
      next := (27720)
      square := (1445676494885490546080109037260000000000000)
      linear := (-243762466423787361567837586675080000000000000)
      constant := (10388392043184171312658573566395786788752402167) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree128.table
  base := (14407173581348316601943228158108524815599/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 19845000000000000000000000000000000000000000
      center := (26145)
      previous := (0)
      next := (13545)
      square := (722838247442745273040054518630000000000000)
      linear := (-123349856952729734672000173946820000000000000)
      constant := (5318757845167767390147092536860332734993112431) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell182.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (340161150956421451619/100000000000000000000)
  centralHi := (17008057547821072581/5000000000000000000)
  directionLo := (341497742160134585377/100000000000000000000)
  directionHi := (170748871080067292689/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 41
  qDenominator := 63
  table := BinomialMassData.Q41_63.Degree129.table
  base := (29630031973370457776552583624545197219949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5740)
      previous := (0)
      next := (3080)
      square := (160630721653943394008901004140000000000000)
      linear := (-27293793399081506179104650620080000000000000)
      constant := (1172320094716535324840320584549404431973997509) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q41_63.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 83
  qDenominator := 126
  table := BinomialMassData.Q83_126.Degree129.table
  base := (29630031973370457395290302908793325908087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4410000000000000000000000000000000000000000
      center := (5810)
      previous := (0)
      next := (3010)
      square := (160630721653943394008901004140000000000000)
      linear := (-27622703924372914081122876485700000000000000)
      constant := (1200432111203541754091109914772192856725466367) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q83_126.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell182.Kernel129
