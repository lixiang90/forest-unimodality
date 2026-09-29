import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage99KernelData.Cell048.Parameters
import ForestUnimodality.BinomialMassData.Q9237_19012.Batch000_049
import ForestUnimodality.BinomialMassData.Q9237_19012.Batch050_099
import ForestUnimodality.BinomialMassData.Q9237_19012.Batch100_149
import ForestUnimodality.BinomialMassData.Q4631_9506.Batch000_049
import ForestUnimodality.BinomialMassData.Q4631_9506.Batch050_099
import ForestUnimodality.BinomialMassData.Q4631_9506.Batch100_149

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree000.table
  base := (5291410514245385692365886161/100000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (106)
      previous := (53)
      next := (53)
      square := (884004480696350264379290710000000000000)
      linear := (24955905374220888233438576000000000000)
      constant := (529141051424538569236588616100000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree000.table
  base := (5291410514245385692365886161/100000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (106)
      previous := (53)
      next := (53)
      square := (884004480696350264379290710000000000000)
      linear := (24955905374220888233438576000000000000)
      constant := (529141051424538569236588616100000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree000.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel000

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree001.table
  base := (38384189455842100054563176624116794618139/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-18841649038126560883188334475710471000000000000)
      constant := (6941540716713663382183097463746440984531237698008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree001.table
  base := (153236983378083478576425332696893225179899/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-18894169954335932793270769085018346000000000000)
      constant := (6928021112857759142270984849036108137656249856182) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree001.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel001

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (6247497085982211447/12500000000000000000)
  directionHi := (49979976687857691577/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree002.table
  base := (184967959808742903436854198836759810082243/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-38247077159165294220446273922784126000000000000)
      constant := (4196921314366473620377274203415062129906242353187) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree002.table
  base := (184310584826254185979485877771817913424373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-38352118991584038040611143141399876000000000000)
      constant := (4182171275021020627148016879870450370531231262357) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree002.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel002

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (6247497085982211447/12500000000000000000)
  centralHi := (49979976687857691577/100000000000000000000)
  directionLo := (14136472175811893999/20000000000000000000)
  directionHi := (17670590219764867499/25000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree003.table
  base := (23310544739272939327768400646627106016129/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-57652505280204027557704213369857781000000000000)
      constant := (2674648555615886850825460391212857075646621920805) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree003.table
  base := (116002521949964624107398947458805555202537/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-57810068028832143287951517197781406000000000000)
      constant := (2662446685831423175900236113488369572330510189833) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree003.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel003

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14136472175811893999/20000000000000000000)
  centralHi := (17670590219764867499/25000000000000000000)
  directionLo := (17313571796895515133/20000000000000000000)
  directionHi := (43283929492238787833/50000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree004.table
  base := (77177461019676953422711820519249278214633/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-77057933401242760894962152816931436000000000000)
      constant := (1817846245573085669633685934398183571390278034697) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree004.table
  base := (7675773584630380126532008293326313866157/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-77268017066080248535291891254162936000000000000)
      constant := (1808770094990640181679154248199846468871775824130) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree004.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel004

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17313571796895515133/20000000000000000000)
  centralHi := (43283929492238787833/50000000000000000000)
  directionLo := (99959953375715383153/100000000000000000000)
  directionHi := (49979976687857691577/50000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree005.table
  base := (53681182063695615714780360531998677316957/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-96463361522281494232220092264005091000000000000)
      constant := (1329194347137957786002848961746784346630471439613) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree005.table
  base := (53370600436207662063309867742924145324809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-96725966103328353782632265310544466000000000000)
      constant := (1322813084895900857594151417476980070850068042281) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree005.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel005

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (99959953375715383153/100000000000000000000)
  centralHi := (49979976687857691577/50000000000000000000)
  directionLo := (111758625387904586243/100000000000000000000)
  directionHi := (27939656346976146561/25000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree006.table
  base := (243698339257392957322727585155624710199/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-115868789643320227569478031711078746000000000000)
      constant := (1048925798466480901324653745434057650096480126560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree006.table
  base := (38761300659364727937247476093411000941887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-116183915140576459029972639366925996000000000000)
      constant := (1044635489801373048599866968711554448977177693983) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree006.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel006

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111758625387904586243/100000000000000000000)
  centralHi := (27939656346976146561/25000000000000000000)
  directionLo := (122425440241449774563/100000000000000000000)
  directionHi := (30606360060362443641/25000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree007.table
  base := (29296966339297804964782918512569561150523/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (48870346)
      previous := (24435173)
      next := (24435173)
      square := (407562309784726022239692568229110000000000000)
      linear := (-2760698321721611447076244309350049000000000000)
      constant := (18182046009981301583555830969150045417398274443) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree007.table
  base := (29122010505442834397632639115101421291387/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (48870346)
      previous := (24435173)
      next := (24435173)
      square := (407562309784726022239692568229110000000000000)
      linear := (-2768201309751521719945163539251174000000000000)
      constant := (18126830164024668035194284129949239873602353867) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree007.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel007

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122425440241449774563/100000000000000000000)
  centralHi := (30606360060362443641/25000000000000000000)
  directionLo := (66117294424438580739/50000000000000000000)
  directionHi := (132234588848877161479/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree008.table
  base := (11260712877256275554807223509202424569843/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-154679645885397694243993910605226056000000000000)
      constant := (808291149471316178148633788523184000558288683174) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree008.table
  base := (22383958170061439388196852719129008167721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-155099813215072669524653387479689056000000000000)
      constant := (806815007151700847950069996156737383678058620489) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree008.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel008

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66117294424438580739/50000000000000000000)
  centralHi := (132234588848877161479/100000000000000000000)
  directionLo := (14136472175811893999/10000000000000000000)
  directionHi := (141364721758118939991/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree009.table
  base := (8760186189509432904977027958567592633483/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-174085074006436427581251850052299711000000000000)
      constant := (775177648431380691932202468543975092957696308694) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree009.table
  base := (8704117154614844512901710534866465142523/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-174557762252320774771993761536070586000000000000)
      constant := (774707365904567915284891146223292877165846751414) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree009.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel009

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14136472175811893999/10000000000000000000)
  centralHi := (141364721758118939991/100000000000000000000)
  directionLo := (14993993006357307473/10000000000000000000)
  directionHi := (149939930063573074731/100000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree010.table
  base := (13650766328702836733364017626353279411549/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-193490502127475160918509789499373366000000000000)
      constant := (777052831559900968417630061797014169865818162941) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree010.table
  base := (13556080724313334839680491043830505395077/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-194015711289568880019334135592452116000000000000)
      constant := (777461562081639840817540201716940251854733062693) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree010.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel010

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14993993006357307473/10000000000000000000)
  centralHi := (149939930063573074731/100000000000000000000)
  directionLo := (7902528186787438321/5000000000000000000)
  directionHi := (158050563735748766421/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree011.table
  base := (10542153815723501223916640035354058828877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-212895930248513894255767728946447021000000000000)
      constant := (805547774001677729676190172460133936564689766893) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree011.table
  base := (5229965447833318715005475341455879854211/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-213473660326816985266674509648833646000000000000)
      constant := (806773897129501048955094188028973063278798777798) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree011.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel011

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (7902528186787438321/5000000000000000000)
  centralHi := (158050563735748766421/100000000000000000000)
  directionLo := (165764829704333788049/100000000000000000000)
  directionHi := (3315296594086675761/2000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree012.table
  base := (3986948578337736403578085904998984647811/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-232301358369552627593025668393520676000000000000)
      constant := (855678047865160739214974652042025716339120262598) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree012.table
  base := (1975249388388515135405126321498885314633/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-232931609364065090514014883705215176000000000000)
      constant := (857701745868470612537084317000873798531367738788) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree012.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel012

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165764829704333788049/100000000000000000000)
  centralHi := (3315296594086675761/2000000000000000000)
  directionLo := (173135717968955151331/100000000000000000000)
  directionHi := (43283929492238787833/25000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree013.table
  base := (1161811915770977470309197220813338621017/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-251706786490591360930283607840594331000000000000)
      constant := (924350113285766048103662379630129877912213180765) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree013.table
  base := (2871745567458212039304496268775564197663/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-252389558401313195761355257761596706000000000000)
      constant := (927177485057372526484409158661027085038965223934) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree013.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel013

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173135717968955151331/100000000000000000000)
  centralHi := (43283929492238787833/25000000000000000000)
  directionLo := (22525671086820718867/12500000000000000000)
  directionHi := (180205368694565750937/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree014.table
  base := (1979269776642141955054855120679384268107/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (48870346)
      previous := (24435173)
      next := (24435173)
      square := (407562309784726022239692568229110000000000000)
      linear := (-5532902339012859066684521373217714000000000000)
      constant := (20603083200417348475346155047122961504704638774) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree014.table
  base := (1949503005778674832228298963184479403319/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (48870346)
      previous := (24435173)
      next := (24435173)
      square := (407562309784726022239692568229110000000000000)
      linear := (-5547908315072679612422359833019964000000000000)
      constant := (20677631476611668431136820300170757137171190158) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree014.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel014

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22525671086820718867/12500000000000000000)
  centralHi := (180205368694565750937/100000000000000000000)
  directionLo := (93503974482456060307/50000000000000000000)
  directionHi := (37401589792982424123/20000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree015.table
  base := (1180704168339853807592243949399024304397/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-290517642732668827604799486734741641000000000000)
      constant := (1109904496681326306808906908918391279678702733146) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree015.table
  base := (461406073325388811736799909275308270193/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-291305456475809406256036005874359766000000000000)
      constant := (1114414094759206002616261899648913040548522473685) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree015.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel015

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93503974482456060307/50000000000000000000)
  centralHi := (37401589792982424123/20000000000000000000)
  directionLo := (9678580867795388549/5000000000000000000)
  directionHi := (193571617355907770981/100000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree016.table
  base := (243491892929265349112410553463969646127/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-309923070853707560942057426181815296000000000000)
      constant := (1224423182884800849822010270570751773805527488572) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree016.table
  base := (1848230057746391246824471787012326157/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-310763405513057511503376379930741296000000000000)
      constant := (1229826381654278538776653913233617667661861206500) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree016.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel016

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9678580867795388549/5000000000000000000)
  centralHi := (193571617355907770981/100000000000000000000)
  directionLo := (199919906751430766307/100000000000000000000)
  directionHi := (49979976687857691577/25000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree017.table
  base := (-236468206190335841636162503075106196497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-329328498974746294279315365628888951000000000000)
      constant := (1352368737806226810421767507830165414613980504527) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree017.table
  base := (-14113750495067420196211730163444514397/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-330221354550305616750716753987122826000000000000)
      constant := (1358705804376185632470687222741542339585134868540) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree017.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel017

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199919906751430766307/100000000000000000000)
  centralHi := (49979976687857691577/25000000000000000000)
  directionLo := (206072723049945577221/100000000000000000000)
  directionHi := (103036361524972788611/50000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree018.table
  base := (-161900456542297316005883425172639079391/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-348733927095785027616573305075962606000000000000)
      constant := (1493169503750072739900173937223578057529809635848) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree018.table
  base := (-1337351117862193003515994258636154149977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-349679303587553721998057128043504356000000000000)
      constant := (1500482812679798047201331561386340111872482243207) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree018.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel018

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206072723049945577221/100000000000000000000)
  centralHi := (103036361524972788611/50000000000000000000)
  directionLo := (106023541318589204993/50000000000000000000)
  directionHi := (212047082637178409987/100000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree019.table
  base := (-2222360115830552545459827051879004665893/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-368139355216823760953831244523036261000000000000)
      constant := (1646370919137649646750306052150874792056769243963) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree019.table
  base := (-1130587048313216274183542351290510574547/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-369137252624801827245397502099885886000000000000)
      constant := (1654704212815236789434203267668636309491627104154) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree019.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel019

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106023541318589204993/50000000000000000000)
  centralHi := (212047082637178409987/100000000000000000000)
  directionLo := (43571533516578076857/20000000000000000000)
  directionHi := (108928833791445192143/50000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree020.table
  base := (-189641347923473158404322934679791163439/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-387544783337862494291089183970109916000000000000)
      constant := (1811604209013315872730074643482070881338065280784) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree020.table
  base := (-191876628044120238198185505279780587593/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-388595201662049932492737876156267416000000000000)
      constant := (1821002175658117580210673383930786187642579978608) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree020.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel020

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43571533516578076857/20000000000000000000)
  centralHi := (108928833791445192143/50000000000000000000)
  directionLo := (111758625387904586243/50000000000000000000)
  directionHi := (223517250775809172487/100000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree021.table
  base := (-748869867550302685169419671257548625867/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (48870346)
      previous := (24435173)
      next := (24435173)
      square := (407562309784726022239692568229110000000000000)
      linear := (-8305106356304106686292798437085379000000000000)
      constant := (40582973879833224455707772004339375994908262265) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree021.table
  base := (-755463436454675243875213835211156236071/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (48870346)
      previous := (24435173)
      next := (24435173)
      square := (407562309784726022239692568229110000000000000)
      linear := (-8327615320393837504899556126788754000000000000)
      constant := (40797423491324874842874891818749828088827950445) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree021.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel021

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111758625387904586243/50000000000000000000)
  centralHi := (223517250775809172487/100000000000000000000)
  directionLo := (229037026404236143597/100000000000000000000)
  directionHi := (114518513202118071799/50000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree022.table
  base := (-4363814113142375016964842368037118481293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-426355639579939960965605062864257226000000000000)
      constant := (2177002643581551060216767173862065893555043505363) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree022.table
  base := (-4394213400312537228007243315315052080423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-427511099736546142987418624269030476000000000000)
      constant := (2188666690050841685094598611068133282615695283193) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree022.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel022

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (229037026404236143597/100000000000000000000)
  centralHi := (114518513202118071799/50000000000000000000)
  directionLo := (117213435166167665231/50000000000000000000)
  directionHi := (234426870332335330463/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree023.table
  base := (-1225512849747777012901343831873691989781/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-445761067700978694302863002311330881000000000000)
      constant := (2376702725460909158569957767946067961957518083884) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree023.table
  base := (-246504468497629317298126943421324257973/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-446969048773794248234758998325412006000000000000)
      constant := (2389569209396398735143728729056330223424272704860) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree023.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel023

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117213435166167665231/50000000000000000000)
  centralHi := (234426870332335330463/100000000000000000000)
  directionLo := (239695547734062764001/100000000000000000000)
  directionHi := (119847773867031382001/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree024.table
  base := (-1341750462421684495631501109660586370991/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-465166495822017427640120941758404536000000000000)
      constant := (2587486578355133929884783208603721249390659920324) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree024.table
  base := (-5392867554731868763767877917411494442993/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-466426997811042353482099372381793536000000000000)
      constant := (2601602332666493089403982232595087896334895150063) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree024.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel024

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239695547734062764001/100000000000000000000)
  centralHi := (119847773867031382001/50000000000000000000)
  directionLo := (244850880482899549127/100000000000000000000)
  directionHi := (30606360060362443641/12500000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree025.table
  base := (-5765413044349559609970929531026659049217/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-484571923943056160977378881205478191000000000000)
      constant := (2809201767643590582246273575287935350554207310047) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree025.table
  base := (-578927929374947939456992253712875989633/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-485884946848290458729439746438175066000000000000)
      constant := (2824613992118955042800608660431315188523169903030) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree025.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel025

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244850880482899549127/100000000000000000000)
  centralHi := (30606360060362443641/12500000000000000000)
  directionLo := (62474970859822114471/25000000000000000000)
  directionHi := (49979976687857691577/20000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree026.table
  base := (-6103045373869568234239184518918003517583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-503977352064094894314636820652551846000000000000)
      constant := (3041718160283839713815415690150124805772250788753) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree026.table
  base := (-6125070305019314854480236916559676987793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-505342895885538563976780120494556596000000000000)
      constant := (3058474386186421194753962120967655694131675446863) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree026.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel026

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62474970859822114471/25000000000000000000)
  centralHi := (49979976687857691577/20000000000000000000)
  directionLo := (254848876420298851503/100000000000000000000)
  directionHi := (15928054776268678219/6250000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree027.table
  base := (-1596209170724326777708311395584826728819/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-523382780185133627651894760099625501000000000000)
      constant := (3284924205382940300052263814285106027798237646516) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree027.table
  base := (-6405165103059903916185420051775603071573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-524800844922786669224120494550938126000000000000)
      constant := (3303072265117082831093520702104470414529666712843) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree027.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel027

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254848876420298851503/100000000000000000000)
  centralHi := (15928054776268678219/6250000000000000000)
  directionLo := (64925894238358181749/25000000000000000000)
  directionHi := (259703576953432726997/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree028.table
  base := (-6615035557161076176439401474492074412453/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (48870346)
      previous := (24435173)
      next := (24435173)
      square := (407562309784726022239692568229110000000000000)
      linear := (-11077310373595354305901075500953044000000000000)
      constant := (72218855573519735623110991189647041520808256427) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree028.table
  base := (-6633800139673218302262872633238162179157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (48870346)
      previous := (24435173)
      next := (24435173)
      square := (407562309784726022239692568229110000000000000)
      linear := (-11107322325714995397376752420557544000000000000)
      constant := (72618610677350072294220262074427236470759277563) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree028.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel028

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (64925894238358181749/25000000000000000000)
  centralHi := (259703576953432726997/100000000000000000000)
  directionLo := (66117294424438580739/25000000000000000000)
  directionHi := (264469177697754322957/100000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree029.table
  base := (-1699327555529201824670937067739046719197/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-562193636427211094326410638993772811000000000000)
      constant := (3803034444528130964331012007094632057035800400908) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree029.table
  base := (-6814632592618982618402559505645359077211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-563716742997282879718801242663701186000000000000)
      constant := (3824110741069948790319115092578791983778494604101) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree029.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel029

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66117294424438580739/25000000000000000000)
  centralHi := (264469177697754322957/100000000000000000000)
  directionLo := (1076601646083416693/400000000000000000)
  directionHi := (269150411520854173251/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree030.table
  base := (-3467419071819076246749407580029510301453/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-581599064548249827663668578440846466000000000000)
      constant := (4077783987499783190893184220404620642528565127846) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree030.table
  base := (-6950829873105221304488365300247828486039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-583174692034530984966141616720082716000000000000)
      constant := (4100397163741361393806850658240497834441436576649) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree030.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel030

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1076601646083416693/400000000000000000)
  centralHi := (269150411520854173251/100000000000000000000)
  directionLo := (136875803277609981283/50000000000000000000)
  directionHi := (273751606555219962567/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree031.table
  base := (-3515190082684759781706923629825191582029/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-601004492669288561000926517887920121000000000000)
      constant := (4362910181773805315752346809002119727462317245478) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree031.table
  base := (-3522571839032009232388497603016906786929/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-602632641071779090213481990776464246000000000000)
      constant := (4387109027594233368491979373397272036748651757278) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree031.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel031

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136875803277609981283/50000000000000000000)
  centralHi := (273751606555219962567/100000000000000000000)
  directionLo := (139138366528864664803/50000000000000000000)
  directionHi := (278276733057729329607/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree032.table
  base := (-1771585534998332976344362862599779811327/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-620409920790327294338184457334993776000000000000)
      constant := (4658358676710596037806223222308477515537173764228) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree032.table
  base := (-7099971541281963989343080038356967441127/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-622090590109027195460822364832845776000000000000)
      constant := (4684192169921214058088516242627782875324792972857) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree032.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel032

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (139138366528864664803/50000000000000000000)
  centralHi := (278276733057729329607/100000000000000000000)
  directionLo := (282729443516237879981/100000000000000000000)
  directionHi := (141364721758118939991/50000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree033.table
  base := (-3552413187767412871981046191804323907519/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-639815348911366027675442396782067431000000000000)
      constant := (4964081979050636473278370890233916607107646206658) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree033.table
  base := (-3558704101899600553149378962487973143871/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-641548539146275300708162738889227306000000000000)
      constant := (4991599268408612917568890900478591398130103888322) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree033.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel033

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282729443516237879981/100000000000000000000)
  centralHi := (141364721758118939991/50000000000000000000)
  directionLo := (4486142299311074323/1562500000000000000)
  directionHi := (287113107155908756673/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree034.table
  base := (-7087674742139723806481324605891184239379/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-659220777032404761012700336229141086000000000000)
      constant := (5280038479088887768724544756193929525327530856589) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree034.table
  base := (-7099288649249213156896025979926324124777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-661006488183523405955503112945608836000000000000)
      constant := (5309288868924651072069529408878545926360245670007) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree034.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel034

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4486142299311074323/1562500000000000000)
  centralHi := (287113107155908756673/100000000000000000000)
  directionLo := (29143083977238775133/10000000000000000000)
  directionHi := (291430839772387751331/100000000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree035.table
  base := (-7036504920348113651583626098504127703417/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (48870346)
      previous := (24435173)
      next := (24435173)
      square := (407562309784726022239692568229110000000000000)
      linear := (-13849514390886601925509352564820709000000000000)
      constant := (114412074118157340433602633189339357834488922903) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree035.table
  base := (-55056439731379327501877250310398332817/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (48870346)
      previous := (24435173)
      next := (24435173)
      square := (407562309784726022239692568229110000000000000)
      linear := (-13887029331036153289853948714326334000000000000)
      constant := (115045399349735648883789338322614763706683840384) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree035.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel035

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (29143083977238775133/10000000000000000000)
  centralHi := (291430839772387751331/100000000000000000000)
  directionLo := (295685529642824998203/100000000000000000000)
  directionHi := (73921382410706249551/25000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree036.table
  base := (-6952740987620639235561913538695064227759/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-698031633274482227687216215123288396000000000000)
      constant := (5942509265806372106081914813193063321775118381169) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree036.table
  base := (-1740658367632166848049820616847673724553/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-699922386258019616450183861058371896000000000000)
      constant := (5975374323915873281319691367099128421038238624092) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree036.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel036

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (295685529642824998203/100000000000000000000)
  centralHi := (73921382410706249551/25000000000000000000)
  directionLo := (14993993006357307473/5000000000000000000)
  directionHi := (299879860127146149461/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree037.table
  base := (-341881965758917086495289942935092382173/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-717437061395520961024474154570362051000000000000)
      constant := (6288962998445313161136209750372541142944966348860) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree037.table
  base := (-855845919038523909807495850549008524899/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-719380335295267721697524235114753426000000000000)
      constant := (6323709871558113486798657367749218837283439735272) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree037.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel037

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (14993993006357307473/5000000000000000000)
  centralHi := (299879860127146149461/100000000000000000000)
  directionLo := (304016329462079285399/100000000000000000000)
  directionHi := (1520081647310396427/500000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree038.table
  base := (-418269410494782088018966246513959205457/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-736842489516559694361732094017435706000000000000)
      constant := (6645527738665887314596893748006637868922209022192) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree038.table
  base := (-837591477439099839650188236647589728967/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-738838284332515826944864609171134956000000000000)
      constant := (6682206227925408020858911823190222282836791538376) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree038.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel038

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (304016329462079285399/100000000000000000000)
  centralHi := (1520081647310396427/500000000000000000)
  directionLo := (154048634081346478867/50000000000000000000)
  directionHi := (61619453632538591547/20000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree039.table
  base := (-3258869228046657541076013285332843270967/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-756247917637598427698990033464509361000000000000)
      constant := (7012181263460799063250246944764985787714990128594) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree039.table
  base := (-1305101241493541329132979285824221867959/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-758296233369763932192204983227516486000000000000)
      constant := (7050841268844610889744290941908189858314707096845) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree039.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel039

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (154048634081346478867/50000000000000000000)
  centralHi := (61619453632538591547/20000000000000000000)
  directionLo := (156062427187834943923/50000000000000000000)
  directionHi := (312124854375669887847/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree040.table
  base := (-6314795771168172666134457002681946041057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-775653345758637161036247972911583016000000000000)
      constant := (7388903855590333393122833398344182772848966943487) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree040.table
  base := (-790244911731814953164827566844488954871/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-777754182407012037439545357283898016000000000000)
      constant := (7429595367751297965672219191056421027360869161288) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree040.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel040

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (156062427187834943923/50000000000000000000)
  centralHi := (312124854375669887847/100000000000000000000)
  directionLo := (316101127471497532841/100000000000000000000)
  directionHi := (158050563735748766421/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree041.table
  base := (-3042129071938988348603954561146398393817/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-795058773879675894373505912358656671000000000000)
      constant := (7775677992773532533462239122417078907510389217294) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree041.table
  base := (-6090863021061290896896123615030628435963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-797212131444260142686885731340279546000000000000)
      constant := (7818451085688033256388808138890783271227503943333) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree041.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel041

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (316101127471497532841/100000000000000000000)
  centralHi := (158050563735748766421/50000000000000000000)
  directionLo := (160014000058175167901/50000000000000000000)
  directionHi := (320028000116350335803/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree042.table
  base := (-5826815885986500638931350900530845803821/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (48870346)
      previous := (24435173)
      next := (24435173)
      square := (407562309784726022239692568229110000000000000)
      linear := (-16621718408177849545117629628688374000000000000)
      constant := (166785471023900576981209026520803363819760562339) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree042.table
  base := (-1166580861262097607610877184358612277197/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (48870346)
      previous := (24435173)
      next := (24435173)
      square := (407562309784726022239692568229110000000000000)
      linear := (-16666736336357311182331145008095124000000000000)
      constant := (167701896010237994731530627461815523185544089615) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree042.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel042

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (160014000058175167901/50000000000000000000)
  centralHi := (320028000116350335803/100000000000000000000)
  directionLo := (323907269026475429069/100000000000000000000)
  directionHi := (32390726902647542907/10000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree043.table
  base := (-1385771053667481415139442894855074166567/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-833869630121753361048021791252803981000000000000)
      constant := (8579320219406356545593618126407568570604669615588) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree043.table
  base := (-2774347619050428384722286755475220286247/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-836128029518756353181566479453042606000000000000)
      constant := (8626406996495399460976855033041458383972822893554) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree043.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel043

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323907269026475429069/100000000000000000000)
  centralHi := (32390726902647542907/10000000000000000000)
  directionLo := (327740624576673935339/100000000000000000000)
  directionHi := (16387031228833696767/5000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree044.table
  base := (-5233612107472488428278751818759842991979/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-853275058242792094385279730699877636000000000000)
      constant := (8996162008522574705581302608671951912129615483189) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree044.table
  base := (-1047756381296299359919241619761664199939/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-855585978556004458428906853509424136000000000000)
      constant := (9045481024944032391827083199269522275021001257745) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree044.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel044

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (327740624576673935339/100000000000000000000)
  centralHi := (16387031228833696767/5000000000000000000)
  directionLo := (331529659408667576099/100000000000000000000)
  directionHi := (3315296594086675761/1000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree045.table
  base := (-2449444996998995937782175902076833088337/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-872680486363830827722537670146951291000000000000)
      constant := (9423002368220189373538047215428989119394762075934) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree045.table
  base := (-4903652072932055469879004965185150309907/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-875043927593252563676247227565805666000000000000)
      constant := (9474603970823583967989975934099336240182538173837) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree045.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel045

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331529659408667576099/100000000000000000000)
  centralHi := (3315296594086675761/1000000000000000000)
  directionLo := (33527587616371375873/10000000000000000000)
  directionHi := (335275876163713758731/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree046.table
  base := (-1134839114061242681821163034861593786659/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-892085914484869561059795609594024946000000000000)
      constant := (9859831390489324413507499431926501197544969804276) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree046.table
  base := (-9087483702792701600592114368480822781/20000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-894501876630500668923587601622187196000000000000)
      constant := (9913765981880024371081281181864725734113511985500) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree046.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel046

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (33527587616371375873/10000000000000000000)
  centralHi := (335275876163713758731/100000000000000000000)
  directionLo := (10593146701436223509/3125000000000000000)
  directionHi := (338980694445959152289/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree047.table
  base := (-1038851020334360423324535616022233783517/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-911491342605908294397053549041098601000000000000)
      constant := (10306640206390727879881095729993244635960853605388) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree047.table
  base := (-259965096493491959208340765150160632099/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-913959825667748774170927975678568726000000000000)
      constant := (10362958240796873434928024731784997906440892833744) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree047.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel047

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10593146701436223509/3125000000000000000)
  centralHi := (338980694445959152289/100000000000000000000)
  directionLo := (342645457108048523419/100000000000000000000)
  directionHi := (17132272855402426171/5000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree048.table
  base := (-936846146803352489837443553144386412163/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-930896770726947027734311488488172256000000000000)
      constant := (10763420870261296836065625240067952881053391830132) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree048.table
  base := (-3751100750995764236936749936658488861593/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-933417774704996879418268349734950256000000000000)
      constant := (10822172849744617515721646308976384376201352782663) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree048.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel048

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342645457108048523419/100000000000000000000)
  centralHi := (17132272855402426171/5000000000000000000)
  directionLo := (173135717968955151331/50000000000000000000)
  directionHi := (346271435937910302663/100000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree049.table
  base := (-3315613322691490065490970875856652712699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (997354)
      previous := (498677)
      next := (498677)
      square := (8317598158871959637544746290390000000000000)
      linear := (-395794335213655044178079728419511000000000000)
      constant := (4677287071242412253902230484633023129626215109) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree049.table
  base := (-103719776821535094193610413952894183883/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (997354)
      previous := (498677)
      next := (498677)
      square := (8317598158871959637544746290390000000000000)
      linear := (-396866190646499368873639618405386000000000000)
      constant := (4702791640577468790856803514595212495963035296) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree049.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel049

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173135717968955151331/50000000000000000000)
  centralHi := (346271435937910302663/100000000000000000000)
  directionLo := (349859836815003841037/100000000000000000000)
  directionHi := (174929918407501920519/50000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree050.table
  base := (-71509330687471549529768181454796395567/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-969707626969024494408827367382319566000000000000)
      constant := (11706869977872009656307092403756934198883133715880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree050.table
  base := (-1431759492130597370311756004682084937291/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-972333672779493089912949097847713316000000000000)
      constant := (11770641527892298305570761747923730504085789166762) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree050.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel050

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349859836815003841037/100000000000000000000)
  centralHi := (174929918407501920519/50000000000000000000)
  directionLo := (353411804395297349977/100000000000000000000)
  directionHi := (176705902197648674989/50000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree051.table
  base := (-1190959162354413074143209406647162278957/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-989113055090063227746085306829393221000000000000)
      constant := (12193526291080695202187884145115921759638243804774) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree051.table
  base := (-2384811461790379093956291948413397916041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-991791621816741195160289471904094846000000000000)
      constant := (12259883545887677808867053668606347585458136524631) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree051.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel051

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353411804395297349977/100000000000000000000)
  centralHi := (176705902197648674989/50000000000000000000)
  directionLo := (35692842637657583129/10000000000000000000)
  directionHi := (356928426376575831291/100000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree052.table
  base := (-1880476807114467002467252776908256309467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1008518483211101961083343246276466876000000000000)
      constant := (12690130042573646153637215815815288931538524217797) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree052.table
  base := (-1883136914648299812475851645504141315307/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1011249570853989300407629845960476376000000000000)
      constant := (12759123663352976710919919177910263126008627725237) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree052.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel052

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35692842637657583129/10000000000000000000)
  centralHi := (356928426376575831291/100000000000000000000)
  directionLo := (360410737389131501873/100000000000000000000)
  directionHi := (180205368694565750937/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree053.table
  base := (-339063442489768637992119695244933848081/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1027923911332140694420601185723540531000000000000)
      constant := (13196676599042375488889434817302495036309389985084) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree053.table
  base := (-679349490639705420217612099068906372713/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1030707519891237405654970220016857906000000000000)
      constant := (13268357279890263606674652506852524834527766525166) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree053.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel053

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (360410737389131501873/100000000000000000000)
  centralHi := (180205368694565750937/50000000000000000000)
  directionLo := (363859722551282543323/100000000000000000000)
  directionHi := (90964930637820635831/25000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree054.table
  base := (-161886726966161540698178264021881344937/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1047329339453179427757859125170614186000000000000)
      constant := (13713161794217125315789833340842866453197980642835) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree054.table
  base := (-405840365274222109643547873313139149307/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1050165468928485510902310594073239436000000000000)
      constant := (13787580259789167714800207649763172081319506438474) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree054.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel054

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363859722551282543323/100000000000000000000)
  centralHi := (90964930637820635831/25000000000000000000)
  directionLo := (36727632072434932369/10000000000000000000)
  directionHi := (367276320724349323691/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree055.table
  base := (-1876424243323280879538839529740123553/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1066734767574218161095117064617687841000000000000)
      constant := (14239581880217520138019099372767149257322592322944) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree055.table
  base := (-121123403889235372160750917812389289511/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1069623417965733616149650968129620966000000000000)
      constant := (14316788883545713735052550256042578423998306786802) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree055.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel055

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (36727632072434932369/10000000000000000000)
  centralHi := (367276320724349323691/100000000000000000000)
  directionLo := (370661427497566715489/100000000000000000000)
  directionHi := (37066142749756671549/10000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree056.table
  base := (351350927728353262195742560731125377763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (48870346)
      previous := (24435173)
      next := (24435173)
      square := (407562309784726022239692568229110000000000000)
      linear := (-22166126442760344784334183756423704000000000000)
      constant := (301549662944190948286630610033138702775289231283) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree056.table
  base := (349454655950989758353696684578799276629/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (48870346)
      previous := (24435173)
      next := (24435173)
      square := (407562309784726022239692568229110000000000000)
      linear := (-22226150346999626967285537595632704000000000000)
      constant := (303183261321007164394375494005125358197296310789) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree056.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel056

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (370661427497566715489/100000000000000000000)
  centralHi := (37066142749756671549/10000000000000000000)
  directionLo := (374015897929824241229/100000000000000000000)
  directionHi := (37401589792982424123/10000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree057.table
  base := (965031657174415547863828176187779413233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1105545623816295627769632943511835151000000000000)
      constant := (15322213570115109171629739589460942166789361422097) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree057.table
  base := (963290342792524763638974475723230573249/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1108539316040229826644331716242384026000000000000)
      constant := (15405150011555388918634518397576477092889343318241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree057.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel057

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (374015897929824241229/100000000000000000000)
  centralHi := (37401589792982424123/10000000000000000000)
  directionLo := (188670274536008654901/50000000000000000000)
  directionHi := (377340549072017309803/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree058.table
  base := (320147771635014794356872828681011658729/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1124951051937334361106890882958908806000000000000)
      constant := (15878419403644331406932776202724109088057258837805) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree058.table
  base := (199892528846851799857871314949185160161/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1127997265077477931891672090298765556000000000000)
      constant := (15964296792606393039997510259213837049966908739592) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree058.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel058

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (188670274536008654901/50000000000000000000)
  centralHi := (377340549072017309803/100000000000000000000)
  directionLo := (76127232458218340711/20000000000000000000)
  directionHi := (95159040572772925889/25000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree059.table
  base := (2258363516857753028266037518621764707989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1144356480058373094444148822405982461000000000000)
      constant := (16444548522119646693851757729478971497489061870901) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree059.table
  base := (2256896238715892937076435982155479750439/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1147455214114726037139012464355147086000000000000)
      constant := (16533417706219408901038172768210319203941485202951) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree059.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel059

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76127232458218340711/20000000000000000000)
  centralHi := (95159040572772925889/25000000000000000000)
  directionLo := (95975871353627567643/25000000000000000000)
  directionHi := (383903485414510270573/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree060.table
  base := (734451854019437415551245394133518546059/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1163761908179411827781406761853056116000000000000)
      constant := (17020598706716655091366505220599390168702743134124) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree060.table
  base := (146823050739186875873536952009371884051/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1166913163151974142386352838411528616000000000000)
      constant := (17112510553118323106819772375769833726338861949180) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree060.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel060

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95975871353627567643/25000000000000000000)
  centralHi := (383903485414510270573/100000000000000000000)
  directionLo := (387143234711815541961/100000000000000000000)
  directionHi := (193571617355907770981/50000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree061.table
  base := (1819491023369898201965683897867863015987/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1183167336300450561118664701300129771000000000000)
      constant := (17606567957925588830212300352929819573784858921766) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree061.table
  base := (3637746852444508255785960735946994048273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1186371112189222247633693212467910146000000000000)
      constant := (17701573351924040321712434294378752319567481777457) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree061.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel061

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (387143234711815541961/100000000000000000000)
  centralHi := (193571617355907770981/50000000000000000000)
  directionLo := (195178048364081338783/50000000000000000000)
  directionHi := (390356096728162677567/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree062.table
  base := (4361807632592270231978878587803140763039/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1202572764421489294455922640747203426000000000000)
      constant := (18202454473520429508446590352633324332706080916351) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree062.table
  base := (2180337359782054326529538580863677088767/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1205829061226470352881033586524291676000000000000)
      constant := (18300604317220907882501216360270855615770858191806) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree062.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel062

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (195178048364081338783/50000000000000000000)
  centralHi := (390356096728162677567/100000000000000000000)
  directionLo := (78708545996623643631/20000000000000000000)
  directionHi := (98385682495779554539/25000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree063.table
  base := (5106212255974361994423827325854245031009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (48870346)
      previous := (24435173)
      next := (24435173)
      square := (407562309784726022239692568229110000000000000)
      linear := (-24938330460051592403942460820291369000000000000)
      constant := (383841972016503153623897649955282283358341420369) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree063.table
  base := (5105173388170784916043055160150569855921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (48870346)
      previous := (24435173)
      next := (24435173)
      square := (407562309784726022239692568229110000000000000)
      linear := (-25005857352320784859762733889401494000000000000)
      constant := (385910241630554588724430422615602448376943673761) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree063.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel063

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (78708545996623643631/20000000000000000000)
  centralHi := (98385682495779554539/25000000000000000000)
  directionLo := (79340753309326296887/20000000000000000000)
  directionHi := (99175941636657871109/25000000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree064.table
  base := (5872131073503313559058625028678592641373/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1241383620663566761130438519641350736000000000000)
      constant := (19423972958912820408175959005913516208468591215357) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree064.table
  base := (5871178653889590684256778545062307606681/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1244744959300966563375714334637054736000000000000)
      constant := (19528564469511228964095911197968287160703298931129) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree064.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel064

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79340753309326296887/20000000000000000000)
  centralHi := (99175941636657871109/25000000000000000000)
  directionLo := (199919906751430766307/50000000000000000000)
  directionHi := (79967962700572306523/20000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree065.table
  base := (6659505611992798498896587989316712687509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1260789048784605494467696459088424391000000000000)
      constant := (20049602142864648591272518812443302534548930006581) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree065.table
  base := (6658632635360477182411188865794565469739/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1264202908338214668623054708693436266000000000000)
      constant := (20157490898464744438174683732621590298177962976651) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree065.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel065

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (199919906751430766307/50000000000000000000)
  centralHi := (79967962700572306523/20000000000000000000)
  directionLo := (201475727155730778051/50000000000000000000)
  directionHi := (402951454311461556103/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree066.table
  base := (7468283136025338067095966433727888501969/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1280194476905644227804954398535498046000000000000)
      constant := (20685142989317848195733453576677089066198978196721) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree066.table
  base := (186687078627027123369438813034348083617/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1283660857375462773870395082749817796000000000000)
      constant := (20796379947789385779295985209786236440644975982120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree066.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel066

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (201475727155730778051/50000000000000000000)
  centralHi := (402951454311461556103/100000000000000000000)
  directionLo := (406039250074965890847/100000000000000000000)
  directionHi := (12688726564842684089/3125000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree067.table
  base := (8298416079586867666220717461905686138973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1299599905026682961142212337982571701000000000000)
      constant := (21330594423708167394111504276536444354091714293757) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree067.table
  base := (8297683124098475594932078935056480379921/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1303118806412710879117735456806199326000000000000)
      constant := (21445230554375923626699310658728888933271118730289) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree067.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel067

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (406039250074965890847/100000000000000000000)
  centralHi := (12688726564842684089/3125000000000000000)
  directionLo := (409103740720076386961/100000000000000000000)
  directionHi := (204551870360038193481/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree068.table
  base := (1829972307006312003387590492522850963419/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1319005333147721694479470277429645356000000000000)
      constant := (21985955476708593133526816111408941792101286498855) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree068.table
  base := (1143648766729041276936733516564631257223/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1322576755449958984365075830862580856000000000000)
      constant := (22104041759494008047821507641701467718508848864056) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree068.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel068

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (409103740720076386961/100000000000000000000)
  centralHi := (204551870360038193481/50000000000000000000)
  directionLo := (206072723049945577221/50000000000000000000)
  directionHi := (412145446099891154443/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree069.table
  base := (5011290396698835697176528743383640295247/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1338410761268760427816728216876719011000000000000)
      constant := (22651225273844622280834601333519246920100375268446) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree069.table
  base := (200439317981267750522368317123714076713/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1342034704487207089612416204918962386000000000000)
      constant := (22772812698467816234330872029920672222522503670850) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree069.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel069

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (206072723049945577221/50000000000000000000)
  centralHi := (412145446099891154443/100000000000000000000)
  directionLo := (207582433511723893121/50000000000000000000)
  directionHi := (415164867023447786243/100000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree070.table
  base := (5458269465377777308176497600015036257591/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (48870346)
      previous := (24435173)
      next := (24435173)
      square := (407562309784726022239692568229110000000000000)
      linear := (-27710534477342840023550737884159034000000000000)
      constant := (476049041349988691044426932192450382162472024462) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree070.table
  base := (10915975896780094629234444520006723958193/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (48870346)
      previous := (24435173)
      next := (24435173)
      square := (407562309784726022239692568229110000000000000)
      linear := (-27785564357641942752239930183170284000000000000)
      constant := (478602910028320071175803979863233050020409258913) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree070.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel070

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (207582433511723893121/50000000000000000000)
  centralHi := (415164867023447786243/100000000000000000000)
  directionLo := (104540621554588733891/25000000000000000000)
  directionHi := (83632497243670987113/20000000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree071.table
  base := (1183170443584976511300396048501282824719/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1377221617510837894491244095770866321000000000000)
      constant := (24011488021752008524975395422330208128422723514710) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree071.table
  base := (11831188986156235203449492603353834516301/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1380950602561703300107096953031725446000000000000)
      constant := (24140230734750924487319552601090087519242266537709) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree071.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel071

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104540621554588733891/25000000000000000000)
  centralHi := (83632497243670987113/20000000000000000000)
  directionLo := (26321173076984486249/6250000000000000000)
  directionHi := (84227753846350355997/20000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree072.table
  base := (6384024437404553242707876170907066745649/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1396627045631876627828502035217939976000000000000)
      constant := (24706479618302470169541932447419083278029114539682) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree072.table
  base := (6383788537721690703527360746880777263979/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1400408551598951405354437327088106976000000000000)
      constant := (24838876493936597674338449844821921234195089929622) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree072.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel072

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26321173076984486249/6250000000000000000)
  centralHi := (84227753846350355997/20000000000000000000)
  directionLo := (106023541318589204993/25000000000000000000)
  directionHi := (424094165274356819973/100000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree073.table
  base := (13725546589150626125300047678734813436989/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1416032473752915361165759974665013631000000000000)
      constant := (25411377236149811486156115771137210291343339431901) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree073.table
  base := (1715639352751682674098342037185840934391/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1419866500636199510601777701144488506000000000000)
      constant := (25547479296429164193916912765078814903271163924152) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree073.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel073

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106023541318589204993/25000000000000000000)
  centralHi := (424094165274356819973/100000000000000000000)
  directionLo := (427029108011939013227/100000000000000000000)
  directionHi := (106757277002984753307/25000000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree074.table
  base := (14704174423703732077288311503674792007599/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1435437901873954094503017914112087286000000000000)
      constant := (26126180352195365235418887221161241420816797077391) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree074.table
  base := (229746552534160507637602230729363786007/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1439324449673447615849118075200870036000000000000)
      constant := (26266038625715018814373602596256639340653325508032) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree074.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel074

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (427029108011939013227/100000000000000000000)
  centralHi := (106757277002984753307/25000000000000000000)
  directionLo := (13435750509629989919/3125000000000000000)
  directionHi := (429944016308159677409/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree075.table
  base := (15703911481435380283763514030445593085023/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1454843329994992827840275853559160941000000000000)
      constant := (26850888494354069845727223959038124726769092358207) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree075.table
  base := (7851775033915500951024605693257013610557/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1458782398710695721096458449257251566000000000000)
      constant := (26994554015783872690723074378101613005078431364026) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree075.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel075

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13435750509629989919/3125000000000000000)
  centralHi := (429944016308159677409/100000000000000000000)
  directionLo := (432839294922387878327/100000000000000000000)
  directionHi := (54104911865298484791/12500000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree076.table
  base := (1672473890247234952833820990063115410087/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1474248758116031561177533793006234596000000000000)
      constant := (27585501236562359637722726259188874713973141077830) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree076.table
  base := (4181102081761349872378297583196071955217/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1478240347747943826343798823313633096000000000000)
      constant := (27733025046174074582864528766339116497219819375812) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree076.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel076

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (432839294922387878327/100000000000000000000)
  centralHi := (54104911865298484791/12500000000000000000)
  directionLo := (43571533516578076857/10000000000000000000)
  directionHi := (435715335165780768571/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree077.table
  base := (1776663966489685596502720196953446368017/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (48870346)
      previous := (24435173)
      next := (24435173)
      square := (407562309784726022239692568229110000000000000)
      linear := (-30482738494634087643159014948026699000000000000)
      constant := (578163636617917076720014039164303406044569256970) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree077.table
  base := (17766337346496044548045611222671567620041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (48870346)
      previous := (24435173)
      next := (24435173)
      square := (407562309784726022239692568229110000000000000)
      linear := (-30565271362963100644717126476939074000000000000)
      constant := (581254108928719960075352101693001667707111322681) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree077.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel077

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (43571533516578076857/10000000000000000000)
  centralHi := (435715335165780768571/100000000000000000000)
  directionLo := (109643128879659927587/25000000000000000000)
  directionHi := (438572515518639710349/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree078.table
  base := (9414799202570682342198497515849123083311/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1513059614358109027852049671900381906000000000000)
      constant := (29084439020422308757154282663536159109934373101598) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree078.table
  base := (9414660986626177809506063597771188989823/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1517156245822440036838479571426396156000000000000)
      constant := (29239832547463491931099005370317815778819584602814) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree078.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel078

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109643128879659927587/25000000000000000000)
  centralHi := (438572515518639710349/100000000000000000000)
  directionLo := (441411202211799636003/100000000000000000000)
  directionHi := (110352800552949909001/25000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree079.table
  base := (9956800628015534518732970450339439782511/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1532465042479147761189307611347455561000000000000)
      constant := (29848763401722004769763106237629969812738328087198) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree079.table
  base := (248916856677115477345445085606783307803/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1536614194859688142085819945482777686000000000000)
      constant := (30008168367152572356595605119905260114910187458160) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree079.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel079

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (441411202211799636003/100000000000000000000)
  centralHi := (110352800552949909001/25000000000000000000)
  directionLo := (222115874887290004667/50000000000000000000)
  directionHi := (88846349954916001867/20000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree080.table
  base := (21018635700721284383444970005281962176553/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1551870470600186494526565550794529216000000000000)
      constant := (30622991055408873874784931003547820135068168411977) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree080.table
  base := (2627300586383962382731912073937159278443/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1556072143896936247333160319539159216000000000000)
      constant := (30786458517842697005405269018816985525549914551896) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree080.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel080

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (222115874887290004667/50000000000000000000)
  centralHi := (88846349954916001867/20000000000000000000)
  directionLo := (447034501551618344973/100000000000000000000)
  directionHi := (223517250775809172487/50000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree081.table
  base := (22144690440954686534855651830315526825431/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1571275898721225227863823490241602871000000000000)
      constant := (31407121726243883177184514050215133709728053149879) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree081.table
  base := (4428895862034423743222814534295324729443/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1575530092934184352580500693595540746000000000000)
      constant := (31574702748010369560737560354336446021603846889935) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree081.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel081

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (447034501551618344973/100000000000000000000)
  centralHi := (223517250775809172487/50000000000000000000)
  directionLo := (449819790190719224191/100000000000000000000)
  directionHi := (3514217110864993939/781250000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree082.table
  base := (465835105564446227630580412233818155743/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1590681326842263961201081429688676526000000000000)
      constant := (32201155183832424882168351280534691612537675734350) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree082.table
  base := (2911445293038694448772576722518534648089/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1594988041971432457827841067651922276000000000000)
      constant := (32372900830680086767356819304705211773214323454408) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree082.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel082

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449819790190719224191/100000000000000000000)
  centralHi := (3514217110864993939/781250000000000000)
  directionLo := (113146984525920271289/25000000000000000000)
  directionHi := (452587938103681085157/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree083.table
  base := (1222991050327730804016993708135743389039/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1610086754963302694538339369135750181000000000000)
      constant := (33005091220202358193641515663780087239844411007020) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree083.table
  base := (24459644726742551854338129583172236682143/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1614445991008680563075181441708303806000000000000)
      constant := (33181052561025010750758793392029094872936422652287) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree083.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel083

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113146984525920271289/25000000000000000000)
  centralHi := (452587938103681085157/100000000000000000000)
  directionLo := (45533925790190796967/10000000000000000000)
  directionHi := (455339257901907969671/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree084.table
  base := (12824439657898260618298869267691780661833/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (48870346)
      previous := (24435173)
      next := (24435173)
      square := (407562309784726022239692568229110000000000000)
      linear := (-33254942511925335262767292011894364000000000000)
      constant := (690182237706508059624547758179136738496224296306) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree084.table
  base := (1603044892209640880918889958789459159841/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (48870346)
      previous := (24435173)
      next := (24435173)
      square := (407562309784726022239692568229110000000000000)
      linear := (-33344978368284258537194322770707864000000000000)
      constant := (693860362330670735437117139715371432648196071696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree084.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel084

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45533925790190796967/10000000000000000000)
  centralHi := (455339257901907969671/100000000000000000000)
  directionLo := (91614810561694457439/20000000000000000000)
  directionHi := (114518513202118071799/25000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree085.table
  base := (6714730676083705749643803167977050700287/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1648897611205380161212855248029897491000000000000)
      constant := (34642670296613023663319116358684414476029559678332) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree085.table
  base := (26858775606242868725215027209101809212141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1653361889083176773569862189821066866000000000000)
      constant := (34827216243403860750317882015437498151327760240269) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree085.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel085

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (91614810561694457439/20000000000000000000)
  centralHi := (114518513202118071799/25000000000000000000)
  directionLo := (115198154262041525127/25000000000000000000)
  directionHi := (460792617048166100509/100000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree086.table
  base := (28089944400349107198243219553352285907263/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1668303039326418894550113187476971146000000000000)
      constant := (35476313014202488495936671896303742324601551598367) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree086.table
  base := (28089810055772962996297380093927756729783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1672819838120424878817202563877448396000000000000)
      constant := (35665227878089746858491583410048600163632338321047) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree086.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel086

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (115198154262041525127/25000000000000000000)
  centralHi := (460792617048166100509/100000000000000000000)
  directionLo := (463495236216961192529/100000000000000000000)
  directionHi := (46349523621696119253/10000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree087.table
  base := (29341938290749571279907862950807561072291/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1687708467447457627887371126924044801000000000000)
      constant := (36319857662286422672111602952683351405827175631619) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree087.table
  base := (14670907805127577121232793887316279662471/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1692277787157672984064542937933829926000000000000)
      constant := (36513192522405213393939457542942326708902798646478) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree087.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel087

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (463495236216961192529/100000000000000000000)
  centralHi := (46349523621696119253/10000000000000000000)
  directionLo := (116545546908047781441/25000000000000000000)
  directionHi := (93236437526438225153/20000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree088.table
  base := (15307449428524037774573139630142568829831/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1707113895568496361224629066371118456000000000000)
      constant := (37173304116196610961613945366339756255435663178958) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree088.table
  base := (1913424177656525862144892918263550809099/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1711735736194921089311883311990211456000000000000)
      constant := (37371110053744674529325800185345050219205004654256) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree088.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel088

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (116545546908047781441/25000000000000000000)
  centralHi := (93236437526438225153/20000000000000000000)
  directionLo := (18754149626586826437/4000000000000000000)
  directionHi := (234426870332335330463/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree089.table
  base := (31908821117483288643824941875802436508757/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1726519323689535094561887005818192111000000000000)
      constant := (38036652263390038291789758378515464973766257965813) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree089.table
  base := (6381743770920306565509517038225035141743/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1731193685232169194559223686046592986000000000000)
      constant := (38238980361459193336827792338095095066062161943435) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree089.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel089

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18754149626586826437/4000000000000000000)
  centralHi := (234426870332335330463/50000000000000000000)
  directionLo := (471510157053878373007/100000000000000000000)
  directionHi := (29469384815867398313/6250000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree090.table
  base := (16611850287393918966912057671892077259297/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1745924751810573827899144945265265766000000000000)
      constant := (38909902002268896972145653374501138806286947721346) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree090.table
  base := (33223607226249129940671689893365394619483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1750651634269417299806564060102974516000000000000)
      constant := (39116803345689791890528126193654097860137292028347) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree090.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel090

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (471510157053878373007/100000000000000000000)
  centralHi := (29469384815867398313/6250000000000000000)
  directionLo := (474151691207246299261/100000000000000000000)
  directionHi := (237075845603623149631/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree091.table
  base := (8639883292261425432150815809176632776131/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (48870346)
      previous := (24435173)
      next := (24435173)
      square := (407562309784726022239692568229110000000000000)
      linear := (-36027146529216582882375569075762029000000000000)
      constant := (812103127369705869743396609816280829181960849484) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree091.table
  base := (34559447968173702186589291068018173931763/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (48870346)
      previous := (24435173)
      next := (24435173)
      square := (407562309784726022239692568229110000000000000)
      linear := (-36124685373605416429671519064476654000000000000)
      constant := (816419977883974624120149174285287208427673945283) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree091.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel091

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (474151691207246299261/100000000000000000000)
  centralHi := (237075845603623149631/50000000000000000000)
  directionLo := (119194647621131316323/25000000000000000000)
  directionHi := (476778590484525265293/100000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree092.table
  base := (17958157617571189726650615225019070808097/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1784735608052651294573660824159413076000000000000)
      constant := (40686105897131475559114906369288465089594713199746) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree092.table
  base := (70148901328279932063050202277220178483/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1789567532343913510301244808215737576000000000000)
      constant := (40902306991999769781273342119697479824110622385664) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree092.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel092

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (119194647621131316323/25000000000000000000)
  centralHi := (476778590484525265293/100000000000000000000)
  directionLo := (239695547734062764001/50000000000000000000)
  directionHi := (479391095468125528003/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree093.table
  base := (37294043464359266038742903808447096122287/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1804141036173690027910918763606486731000000000000)
      constant := (41589059895569269011625890235053310881897450717583) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree093.table
  base := (18646986256353655839629290478887325844149/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1809025481381161615548585182272119106000000000000)
      constant := (41809987499340799239423110362210834961762205312682) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree093.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel093

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239695547734062764001/50000000000000000000)
  centralHi := (479391095468125528003/100000000000000000000)
  directionLo := (240994720110134488843/50000000000000000000)
  directionHi := (481989440220268977687/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree094.table
  base := (38692714869707689100614648979098661534737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1823546464294728761248176703053560386000000000000)
      constant := (42501915168949879994227304706256519556119197379633) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree094.table
  base := (9673162533399997841956248352739253061851/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1828483430418409720795925556328500636000000000000)
      constant := (42727620372090667336555546238417070056294213990636) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree094.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel094

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (240994720110134488843/50000000000000000000)
  centralHi := (481989440220268977687/100000000000000000000)
  directionLo := (242286926263865422357/50000000000000000000)
  directionHi := (96914770505546168943/20000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree095.table
  base := (40112326754637734896880694573602523926283/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1842951892415767494585434642500634041000000000000)
      constant := (43424671656355525136623595993141023034816374589547) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree095.table
  base := (4011226769620627448380356588280842483479/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1847941379455657826043265930384882166000000000000)
      constant := (43655205550461114584080216485130730028218564403110) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree095.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel095

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (242286926263865422357/50000000000000000000)
  centralHi := (96914770505546168943/20000000000000000000)
  directionLo := (487144554134895198943/100000000000000000000)
  directionHi := (15223267316715474967/3125000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree096.table
  base := (41552876684792732455608283730882539492357/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1862357320536806227922692581947707696000000000000)
      constant := (44357329302791630975677792438063438403614692418213) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree096.table
  base := (20776411406001120797015053225921423200391/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1867399328492905931290606304441263696000000000000)
      constant := (44592742980492975621367233944175796385625683769038) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree096.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel096

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (487144554134895198943/100000000000000000000)
  centralHi := (15223267316715474967/3125000000000000000)
  directionLo := (244850880482899549127/50000000000000000000)
  directionHi := (97940352193159819651/20000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree097.table
  base := (2150718123125623973105076283562049359347/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (254506)
      previous := (127253)
      next := (127253)
      square := (2122494758151936984774676994710000000000000)
      linear := (-199996040881905086753103467041639000000000000)
      constant := (4814527373643409087252288058258751985235842940) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree097.table
  base := (2688394582833254059704260820014433204199/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 24010000000000000000000000000000000000000000
      center := (254506)
      previous := (127253)
      next := (127253)
      square := (2122494758151936984774676994710000000000000)
      linear := (-200537493626331601290035782601514000000000000)
      constant := (4840071486182145843656785467664079965972508784) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree097.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel097

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (244850880482899549127/50000000000000000000)
  centralHi := (97940352193159819651/20000000000000000000)
  directionLo := (246122841667897331549/50000000000000000000)
  directionHi := (492245683335794663099/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree098.table
  base := (889935642076346646015937190916145957737/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (997354)
      previous := (498677)
      next := (498677)
      square := (8317598158871959637544746290390000000000000)
      linear := (-791823480540976132693547880400606000000000000)
      constant := (19263785039147454615045632968018166365817371650) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree098.table
  base := (44496737290703459555765087453799045442963/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 94090000000000000000000000000000000000000000
      center := (997354)
      previous := (498677)
      next := (498677)
      square := (8317598158871959637544746290390000000000000)
      linear := (-793967191406664782084667660372356000000000000)
      constant := (19365961851518111090690349097907873218572838867) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree098.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel098

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (246122841667897331549/50000000000000000000)
  centralHi := (492245683335794663099/100000000000000000000)
  directionLo := (494776526153416289967/100000000000000000000)
  directionHi := (30923532884588518123/6250000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree099.table
  base := (46000133817631463384736843648792373186867/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1920573604899922427934466400288928661000000000000)
      constant := (47214708723476028121281747838036041575170871078803) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree099.table
  base := (2875005809518619097080846873855273037823/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1925773175604650247032627426610408286000000000000)
      constant := (47465068316848787094587299598260264767818667734512) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree099.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel099

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (494776526153416289967/100000000000000000000)
  centralHi := (30923532884588518123/6250000000000000000)
  directionLo := (124323622278250341037/25000000000000000000)
  directionHi := (497294489113001364149/100000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree100.table
  base := (5940551998378399544581722704773019943827/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1939979033020961161271724339736002316000000000000)
      constant := (48186970555531777184692205842158208442065402011544) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree100.table
  base := (23762189362739680674234542736450086409981/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1945231124641898352279967800666789816000000000000)
      constant := (48442414311750690262989939633398213660277316921658) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree100.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel100

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (124323622278250341037/25000000000000000000)
  centralHi := (497294489113001364149/100000000000000000000)
  directionLo := (62474970859822114471/12500000000000000000)
  directionHi := (499799766878576915769/100000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree101.table
  base := (49069627152293619648692675665604412583173/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1959384461141999894608982279183075971000000000000)
      constant := (49169133342183943380328322401490424490481174491557) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree101.table
  base := (6133699147513294227335711739282975702051/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1964689073679146457527308174723171346000000000000)
      constant := (49429712357892355343369398039738840854554523675672) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree101.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel101

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (62474970859822114471/12500000000000000000)
  centralHi := (499799766878576915769/100000000000000000000)
  directionLo := (251146274629745717091/50000000000000000000)
  directionHi := (502292549259491434183/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree102.table
  base := (50635765995651881024497368261587232470673/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1978789889263038627946240218630149626000000000000)
      constant := (50161197053662572797308905435434568352530065979057) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree102.table
  base := (50635735025471418785598270314374946759141/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1984147022716394562774648548779552876000000000000)
      constant := (50426962426115398396105502945315476793610275163269) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree102.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel102

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (251146274629745717091/50000000000000000000)
  centralHi := (502292549259491434183/100000000000000000000)
  directionLo := (504773021378240288389/100000000000000000000)
  directionHi := (50477302137824028839/10000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree103.table
  base := (26111415663728443330372556696203938437117/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-1998195317384077361283498158077223281000000000000)
      constant := (51163161663092382414265426378438050070511712162106) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree103.table
  base := (52222803096709076902605406781381012964837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-2003604971753642668021988922835934406000000000000)
      constant := (51434164490104332893489867825030608741817749350533) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree103.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel103

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (504773021378240288389/100000000000000000000)
  centralHi := (50477302137824028839/10000000000000000000)
  directionLo := (507241363830904690857/100000000000000000000)
  directionHi := (253620681915452345429/50000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree104.table
  base := (53830822073740753828614443249966415091383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-2017600745505116094620756097524296936000000000000)
      constant := (52175027146211354126760134891854873837027169175447) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree104.table
  base := (53830796342529053336292315013328882076601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-2023062920790890773269329296892315936000000000000)
      constant := (52451318526109450775148345695621718998952431880409) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree104.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel104

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (507241363830904690857/100000000000000000000)
  centralHi := (253620681915452345429/50000000000000000000)
  directionLo := (254848876420298851503/50000000000000000000)
  directionHi := (509697752840597703007/100000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree105.table
  base := (55459737264967463452513633774677814545703/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (48870346)
      previous := (24435173)
      next := (24435173)
      square := (407562309784726022239692568229110000000000000)
      linear := (-41571554563799078121592123203497359000000000000)
      constant := (1085648846553401857184329931778151788670965456823) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree105.table
  base := (55459713814145450750374907640629185151849/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (48870346)
      previous := (24435173)
      next := (24435173)
      square := (407562309784726022239692568229110000000000000)
      linear := (-41684099384247732214625911652014234000000000000)
      constant := (1091396418626463699903752381893176077651593614809) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree105.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel105

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254848876420298851503/50000000000000000000)
  centralHi := (509697752840597703007/100000000000000000000)
  directionLo := (512142360404286243737/100000000000000000000)
  directionHi := (256071180202143121869/50000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree106.table
  base := (14277394006470219547447024794310420232233/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-2056411601747193561295271976418444246000000000000)
      constant := (54228460648035473764068375842804384182540631172388) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree106.table
  base := (57109554655285214345333266843652812183297/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-2061978818865386983764010045005078996000000000000)
      constant := (54515482430522072166462983217319833558908172176673) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree106.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel106

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (512142360404286243737/100000000000000000000)
  centralHi := (256071180202143121869/50000000000000000000)
  directionLo := (514575354433335274203/100000000000000000000)
  directionHi := (128643838608333818551/25000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree107.table
  base := (3673771097896235539616969533331473696663/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-2075817029868232294632529915865517901000000000000)
      constant := (55270028629117614788073957898234680087608233647472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree107.table
  base := (11756063618634124046109619420526930877111/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-2081436767902635089011350419061460526000000000000)
      constant := (55562492262127674873273199688623663010435962474995) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree107.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel107

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (514575354433335274203/100000000000000000000)
  centralHi := (128643838608333818551/25000000000000000000)
  directionLo := (258498449444049576267/50000000000000000000)
  directionHi := (103399379777619830507/20000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree108.table
  base := (60472021173043846773807571697266768224377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-2095222457989271027969787855312591556000000000000)
      constant := (56321497408248940847890806903042430074357814826393) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree108.table
  base := (30236001715190397957443857434540482449973/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-2100894716939883194258690793117842056000000000000)
      constant := (56619453991758088208479507843447941987783364185514) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree108.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel108

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (258498449444049576267/50000000000000000000)
  centralHi := (103399379777619830507/20000000000000000000)
  directionLo := (519407153906865453993/100000000000000000000)
  directionHi := (259703576953432726997/50000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree109.table
  base := (31092313101032075914089624052192321937401/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-2114627886110309761307045794759665211000000000000)
      constant := (57382866970882446995145283732168186522612446855218) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree109.table
  base := (31092305018753276904575201909810264600369/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-2120352665977131299506031167174223586000000000000)
      constant := (57686367605194323550571563405515944473258634964642) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree109.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel109

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (519407153906865453993/100000000000000000000)
  centralHi := (259703576953432726997/50000000000000000000)
  directionLo := (32612892245589888669/6250000000000000000)
  directionHi := (104361255185887643741/20000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree110.table
  base := (63918152072099568020507350829959702818333/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-2134033314231348494644303734206738866000000000000)
      constant := (58454137303885954491620904995119389813506286167997) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree110.table
  base := (63918137346521184082855204538220173561733/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-2139810615014379404753371541230605116000000000000)
      constant := (58763233089604084385528582546331430294914672258597) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree110.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel110

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (32612892245589888669/6250000000000000000)
  centralHi := (104361255185887643741/20000000000000000000)
  directionLo := (262097208907815257213/50000000000000000000)
  directionHi := (524194417815630514427/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree111.table
  base := (32836299129194433003233580995303973455401/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-2153438742352387227981561673653812521000000000000)
      constant := (59535308395404577682348966891270051094508450179218) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree111.table
  base := (65672584844797400978383233396070485070519/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-2159268564051627510000711915286986646000000000000)
      constant := (59850050433406603087154625247266013346362460363671) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree111.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel111

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (262097208907815257213/50000000000000000000)
  centralHi := (524194417815630514427/100000000000000000000)
  directionLo := (526571728958920288867/100000000000000000000)
  directionHi := (131642932239730072217/25000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree112.table
  base := (33723982143607264966600727791381166829277/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (48870346)
      previous := (24435173)
      next := (24435173)
      square := (407562309784726022239692568229110000000000000)
      linear := (-44343758581090325741200400267365024000000000000)
      constant := (1237273066015031834759998554127725577072273394714) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree112.table
  base := (16861988017426861733919756258090774606391/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (48870346)
      previous := (24435173)
      next := (24435173)
      square := (407562309784726022239692568229110000000000000)
      linear := (-44463806389568890107103107945783024000000000000)
      constant := (1243812645431645955525727764282744563261220452124) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree112.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel112

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (526571728958920288867/100000000000000000000)
  centralHi := (131642932239730072217/25000000000000000000)
  directionLo := (528938355395508645913/100000000000000000000)
  directionHi := (264469177697754322957/50000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree113.table
  base := (1731106243273520825541418233393087644021/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-2192249598594464694656077552547959831000000000000)
      constant := (61727352812221178601906653096806006742529688287560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree113.table
  base := (69244238603749503887922737762153655377219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-2198184462126123720495392663399749706000000000000)
      constant := (62053540658404443256882798509213687893509652823971) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree113.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel113

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (528938355395508645913/100000000000000000000)
  centralHi := (264469177697754322957/50000000000000000000)
  directionLo := (132823609977251457913/25000000000000000000)
  directionHi := (531294439909005831653/100000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree114.table
  base := (14212290840706844299876274513405727392941/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-2211655026715503427993335491995033486000000000000)
      constant := (62838226119137546290773700435920397642427383337345) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree114.table
  base := (71061444070149105999163940328541056408459/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-2217642411163371825742733037456131236000000000000)
      constant := (63170213521656262046850890709265092176193004945131) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree114.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel114

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132823609977251457913/25000000000000000000)
  centralHi := (531294439909005831653/100000000000000000000)
  directionLo := (66705015266369660599/12500000000000000000)
  directionHi := (533640122130957284793/100000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree115.table
  base := (72899577356519118638604681361546167851773/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-2231060454836542161330593431442107141000000000000)
      constant := (63959000147613248079703812647518653681229914508957) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree115.table
  base := (72899568128889251663675202441386650895167/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-2237100360200619930990073411512512766000000000000)
      constant := (64296838208224781047236934220777301580352575753503) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree115.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel115

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (66705015266369660599/12500000000000000000)
  centralHi := (533640122130957284793/100000000000000000000)
  directionLo := (535975538637410023723/100000000000000000000)
  directionHi := (133993884659352505931/25000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree116.table
  base := (14951723775065364150864958301392341584433/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-2250465882957580894667851370889180796000000000000)
      constant := (65089674890541859552630779452163602552325000814485) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree116.table
  base := (74758610473127427734170210948576445308347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-2256558309237868036237413785568894296000000000000)
      constant := (65433414711178118281947965617754090509148874852123) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree116.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel116

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (535975538637410023723/100000000000000000000)
  centralHi := (133993884659352505931/25000000000000000000)
  directionLo := (1076601646083416693/200000000000000000)
  directionHi := (538300823041708346501/100000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree117.table
  base := (19159644618999818315072369066700103409613/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-2269871311078619628005109310336254451000000000000)
      constant := (66230250341508481742774085519381500437084991878068) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree117.table
  base := (9579821353245229181346075009897108425307/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-2276016258275116141484754159625275826000000000000)
      constant := (66579943024260782677901320718141006693580690118104) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree117.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel117

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1076601646083416693/200000000000000000)
  centralHi := (538300823041708346501/100000000000000000000)
  directionLo := (54061610608369725281/10000000000000000000)
  directionHi := (540616106083697252811/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree118.table
  base := (78539455902213230541684960504828240268547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-2289276739199658361342367249783328106000000000000)
      constant := (67380726494722513901540262321745707804860907693923) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree118.table
  base := (78539448937512768476630643874763280169087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-2295474207312364246732094533681657356000000000000)
      constant := (67736423141827739675870150241253745533169365938783) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree118.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel118

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54061610608369725281/10000000000000000000)
  centralHi := (540616106083697252811/100000000000000000000)
  directionLo := (542921515715502105857/100000000000000000000)
  directionHi := (271460757857751052929/50000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree119.table
  base := (80461250922593657523495282492286159633281/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (48870346)
      previous := (24435173)
      next := (24435173)
      square := (407562309784726022239692568229110000000000000)
      linear := (-47115962598381573360808677331232689000000000000)
      constant := (1398798027448101235289271603932615793698487505521) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree119.table
  base := (1257206946598257307154268939146865833823/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (48870346)
      previous := (24435173)
      next := (24435173)
      square := (407562309784726022239692568229110000000000000)
      linear := (-47243513394890047999580304239551814000000000000)
      constant := (1406180715485406179180350898104482544437061743552) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree119.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel119

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (542921515715502105857/100000000000000000000)
  centralHi := (271460757857751052929/50000000000000000000)
  directionLo := (545217177184043788279/100000000000000000000)
  directionHi := (13630429429601094707/2500000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree120.table
  base := (41201981664144129308998876754413345597733/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-2328087595441735828016883128677475416000000000000)
      constant := (69711380887493637536383320781853330280236993165194) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree120.table
  base := (41201978778403829828110565472154093861033/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-2334390105386860457226775281794420416000000000000)
      constant := (70079238770535424757668035519341418687602882504594) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree120.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel120

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (545217177184043788279/100000000000000000000)
  centralHi := (13630429429601094707/2500000000000000000)
  directionLo := (547503213110439925133/100000000000000000000)
  directionHi := (273751606555219962567/50000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree121.table
  base := (84367592930777753007782955188998506264587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-2347493023562774561354141068124549071000000000000)
      constant := (70891559118073704153547675362232500716384841298283) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree121.table
  base := (42183793838726914531328224615408778865013/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-2353848054424108562474115655850801946000000000000)
      constant := (71265574272931223257208911562086764937537036936234) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree121.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel121

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (547503213110439925133/100000000000000000000)
  centralHi := (273751606555219962567/50000000000000000000)
  directionLo := (109955948713286921469/20000000000000000000)
  directionHi := (274889871783217303673/50000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree122.table
  base := (86352139559898982642931689753635434412397/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-2366898451683813294691399007571622726000000000000)
      constant := (72081638032853002945693225287533762231029370338573) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree122.table
  base := (8635213477853860050498367748043663936743/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-2373306003461356667721456029907183476000000000000)
      constant := (72461861562229230699231175482652144505879365436870) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree122.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel122

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (109955948713286921469/20000000000000000000)
  centralHi := (274889871783217303673/50000000000000000000)
  directionLo := (110409377229598282583/20000000000000000000)
  directionHi := (138011721536997853229/25000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree123.table
  base := (88357603062060166784672656012777843669709/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-2386303879804852028028656947018696381000000000000)
      constant := (73281617628361740611824361443633026068717989046381) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree123.table
  base := (17671519742110772867575282842015341497319/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-2392763952498604772968796403963565006000000000000)
      constant := (73668100635051908033164271737195486655020035024355) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree123.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel123

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110409377229598282583/20000000000000000000)
  centralHi := (138011721536997853229/25000000000000000000)
  directionLo := (27715237802308867779/5000000000000000000)
  directionHi := (554304756046177355581/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree124.table
  base := (90383983298629627770591761459131330735871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-2405709307925890761365914886465770036000000000000)
      constant := (74491497901468087674184388104971171798836038383839) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree124.table
  base := (45191989669297124980519123780430813354657/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-2412221901535852878216136778019946536000000000000)
      constant := (74884291488351606817628568682745213880744752957826) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree124.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel124

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (27715237802308867779/5000000000000000000)
  centralHi := (554304756046177355581/100000000000000000000)
  directionLo := (556553466115458659213/100000000000000000000)
  directionHi := (278276733057729329607/50000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree125.table
  base := (9243128014448112798851764361212444237501/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-2425114736046929494703172825912843691000000000000)
      constant := (75711278849345316172740603512207347396188832285090) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree125.table
  base := (288847739190416704972506566207309455707/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-2431679850573100983463477152076328066000000000000)
      constant := (76110434119378404588490573748154933546991820276160) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree125.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel125

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (556553466115458659213/100000000000000000000)
  centralHi := (278276733057729329607/50000000000000000000)
  directionLo := (558793126939522931217/100000000000000000000)
  directionHi := (279396563469761465609/50000000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree126.table
  base := (94499493486680596853245199651931017266087/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (48870346)
      previous := (24435173)
      next := (24435173)
      square := (407562309784726022239692568229110000000000000)
      linear := (-49888166615672820980416954395100354000000000000)
      constant := (1570223683049839418418285794299855809631374016567) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree126.table
  base := (94499490207738681312076387494313461817007/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 4610410000000000000000000000000000000000000000
      center := (48870346)
      previous := (24435173)
      next := (24435173)
      square := (407562309784726022239692568229110000000000000)
      linear := (-50023220400211205892057500533320604000000000000)
      constant := (1578500582156144388354675804724593266749574724287) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree126.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel126

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (558793126939522931217/100000000000000000000)
  centralHi := (279396563469761465609/50000000000000000000)
  directionLo := (561023846894736361843/100000000000000000000)
  directionHi := (140255961723684090461/25000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree127.table
  base := (12073577902912563256778651222982857551919/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-2463925592289006961377688704806991001000000000000)
      constant := (78180542759455887954039307475139154460783960770168) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree127.table
  base := (48294310119955976246245749911577361658741/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-2470595748647597193958157900189091126000000000000)
      constant := (78592574704930887448486696468176275392357745719338) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree127.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel127

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (561023846894736361843/100000000000000000000)
  centralHi := (140255961723684090461/25000000000000000000)
  directionLo := (112649146442267796681/20000000000000000000)
  directionHi := (281622866105669491703/50000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree128.table
  base := (12337333657793685872825171718241920569067/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-2483331020410045694714946644254064656000000000000)
      constant := (79430025717308407691205252924512810142024621748824) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree128.table
  base := (98698666548042278581343421412425030511381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-2490053697684845299205498274245472656000000000000)
      constant := (79848572655197959838585404055597348784107882773429) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree128.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel128

namespace ForestUnimodality.Stage99KernelData.Cell048.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (112649146442267796681/20000000000000000000)
  centralHi := (281622866105669491703/50000000000000000000)
  directionLo := (565458887032475759963/100000000000000000000)
  directionHi := (141364721758118939991/25000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 9237
  qDenominator := 19012
  table := BinomialMassData.Q9237_19012.Degree129.table
  base := (100829631520805990042333784645680641153481/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-2502736448531084428052204583701138311000000000000)
      constant := (80689409341124150139876027459954997613799059652329) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q9237_19012.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 4631
  qDenominator := 9506
  table := BinomialMassData.Q4631_9506.Degree129.table
  base := (1260370363143268521760696440253519309571/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 225910090000000000000000000000000000000000000000
      center := (2394646954)
      previous := (1197323477)
      next := (1197323477)
      square := (19970553179451575089744935843226390000000000000)
      linear := (-2509511646722093404452838648301854186000000000000)
      constant := (81114522374629916668128429164568085301835379771120) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q4631_9506.Degree129.checked
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
end ForestUnimodality.Stage99KernelData.Cell048.Kernel129
