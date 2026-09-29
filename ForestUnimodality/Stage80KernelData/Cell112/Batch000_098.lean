import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage80KernelData.Cell112.Parameters
import ForestUnimodality.BinomialMassData.Q27_52.Batch000_049
import ForestUnimodality.BinomialMassData.Q27_52.Batch050_099
import ForestUnimodality.BinomialMassData.Q22597_43472.Batch000_049
import ForestUnimodality.BinomialMassData.Q22597_43472.Batch050_099

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree000.table
  base := (42890720884802540014959504771/1000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (86)
      previous := (43)
      next := (43)
      square := (1133827994043947462454724500000000000000)
      linear := (-40936842069338244542997529000000000000)
      constant := (428907208848025400149595047710000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree000.table
  base := (42890720884802540014959504771/1000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (86)
      previous := (43)
      next := (43)
      square := (1133827994043947462454724500000000000000)
      linear := (-40936842069338244542997529000000000000)
      constant := (428907208848025400149595047710000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree000.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel000

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree001.table
  base := (14614813029305163579318689468491233984699/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-205905139264430942988570732151000000000000)
      constant := (39573706677111374105694477741001296694626096) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree001.table
  base := (46724360943272139790076785339749791960459/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-9003769296521537412107162796295643500000000000)
      constant := (1727035603253481372586735915158969631933589094255) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree001.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel001

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (390318417364746481/781250000000000000)
  directionHi := (49960757422687549569/100000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree002.table
  base := (26931510116887621450404290902800172475209/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-404891952219143722649374881901000000000000)
      constant := (22970950616467718412541295419330645741551605) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree002.table
  base := (134439598259965558556812607994380586667587/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-17705339181508275731894153506733206000000000000)
      constant := (1001805503420859343499840982571773113589840649243) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree002.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel002

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (390318417364746481/781250000000000000)
  centralHi := (49960757422687549569/100000000000000000000)
  directionLo := (17663795183399252579/25000000000000000000)
  directionHi := (70655180733597010317/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree003.table
  base := (161564040285787993490595854152778222141/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-603878765173856502310179031651000000000000)
      constant := (14455530243331062999953062632922094005416448) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree003.table
  base := (41275360383608615029412625725949298047809/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-26406909066495014051681144217170768500000000000)
      constant := (630222094052330424025553951472741158118529586002) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree003.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel003

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17663795183399252579/25000000000000000000)
  centralHi := (70655180733597010317/100000000000000000000)
  directionLo := (86534570240718750803/100000000000000000000)
  directionHi := (21633642560179687701/25000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree004.table
  base := (27144019739583864704278996364395543508693/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-802865578128569281970983181401000000000000)
      constant := (10015608111203721694010387064344693705938234) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree004.table
  base := (10833041160481108672748344812820110936581/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-35108478951481752371468134927608331000000000000)
      constant := (436665725612469360334571831470867761118571488545) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree004.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel004

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (86534570240718750803/100000000000000000000)
  centralHi := (21633642560179687701/25000000000000000000)
  directionLo := (390318417364746481/390625000000000000)
  directionHi := (99921514845375099137/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree005.table
  base := (9435520566454570127335557988138672491427/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-1001852391083282061631787331151000000000000)
      constant := (7687873891846895467324411991611742604204652) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree005.table
  base := (18827053244980406819343575823697095619769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-43810048836468490691255125638045893500000000000)
      constant := (335290477289548813288662175479072436953914834882) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree005.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel005

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (390318417364746481/390625000000000000)
  centralHi := (99921514845375099137/100000000000000000000)
  directionLo := (2234312996090131093/2000000000000000000)
  directionHi := (111715649804506554651/100000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree006.table
  base := (13683015373967509901430859984005753650499/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-1200839204037994841292591480901000000000000)
      constant := (6506173810981109757726880734737444733868662) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree006.table
  base := (27301179567078109746010639972705046538467/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-52511618721455229011042116348483456000000000000)
      constant := (283898532571892391590814831368741139983605317563) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree006.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel006

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2234312996090131093/2000000000000000000)
  centralHi := (111715649804506554651/100000000000000000000)
  directionLo := (122378362848551681721/100000000000000000000)
  directionHi := (61189181424275840861/50000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree007.table
  base := (10161811746932154482958675074712733246081/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-1399826016992707620953395630651000000000000)
      constant := (5991179686656899688597144273972403837175378) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree007.table
  base := (10136752704414451899693823784434689423413/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-61213188606441967330829107058921018500000000000)
      constant := (261577026658431083745200151115552195162611899514) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree007.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel007

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122378362848551681721/100000000000000000000)
  centralHi := (61189181424275840861/50000000000000000000)
  directionLo := (132183739452855560237/100000000000000000000)
  directionHi := (66091869726427780119/50000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree008.table
  base := (15187012896383661631061043284944901067973/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-1598812829947420400614199780401000000000000)
      constant := (5901585273253665063836477222513688280487437) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree008.table
  base := (15146294017080583510866393426812016507451/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-69914758491428705650616097769358581000000000000)
      constant := (257808032976640112039664459602002877627472445139) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree008.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel008

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132183739452855560237/100000000000000000000)
  centralHi := (66091869726427780119/50000000000000000000)
  directionLo := (141310361467194020633/100000000000000000000)
  directionHi := (70655180733597010317/50000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree009.table
  base := (140255824067584383423655358090615491333/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-1797799642902133180275003930151000000000000)
      constant := (6113051688686816599421216927444121442822160) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree009.table
  base := (11185966682625953480624062848424530968123/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-78616328376415443970403088479796143500000000000)
      constant := (267176208206646840592325154496148636155565148947) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree009.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel009

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141310361467194020633/100000000000000000000)
  centralHi := (70655180733597010317/50000000000000000000)
  directionLo := (1170955252094239443/781250000000000000)
  directionHi := (29976454453612529741/20000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree010.table
  base := (4015557612207582759242737781154053914577/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-1996786455856845959935808079901000000000000)
      constant := (6559184349704742908019864204852570223127026) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree010.table
  base := (400050367016337853835119455398947832453/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-87317898261402182290190079190233706000000000000)
      constant := (286791345910670861641226066542927039048002686340) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree010.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel010

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1170955252094239443/781250000000000000)
  centralHi := (29976454453612529741/20000000000000000000)
  directionLo := (3949744677071409353/2500000000000000000)
  directionHi := (157989787082856374121/100000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree011.table
  base := (2699108538406283088244850742600692961217/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-2195773268811558739596612229651000000000000)
      constant := (7202677568202662531601187504647534220891346) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree011.table
  base := (1342865582724991055363869400617497905063/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (5246774)
      previous := (2623387)
      next := (2623387)
      square := (69173712088627190736900287020500000000000000)
      linear := (-793549323523875376941959255377448500000000000)
      constant := (2603551476033133644326514804118456859384954268) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree011.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel011

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (3949744677071409353/2500000000000000000)
  centralHi := (157989787082856374121/100000000000000000000)
  directionLo := (165701086613018080971/100000000000000000000)
  directionHi := (41425271653254520243/25000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree012.table
  base := (1594659606040300914592075622395181895377/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-2394760081766271519257416379401000000000000)
      constant := (8021146910462974181801345402906571480637426) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree012.table
  base := (1582659065428794860495158433879605330431/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-104721038031375658929764060611108831000000000000)
      constant := (350916820695069871427171361656077195668232100718) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree012.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel012

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (165701086613018080971/100000000000000000000)
  centralHi := (41425271653254520243/25000000000000000000)
  directionLo := (173069140481437501607/100000000000000000000)
  directionHi := (21633642560179687701/12500000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree013.table
  base := (1318797739403437791280470061539905300517/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (86)
      previous := (43)
      next := (43)
      square := (1133827994043947462454724500000000000000)
      linear := (-15347614761662628987681778279000000000000)
      constant := (53255159401998827200039088413539905300517) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree013.table
  base := (1297184130259103373015966321477391936741/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (3756566)
      previous := (1878283)
      next := (1878283)
      square := (49526740607833669107484820884500000000000000)
      linear := (-671139691812795249997343498944061500000000000)
      constant := (2330309237358033635335594972446138222813783621) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree013.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel013

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173069140481437501607/100000000000000000000)
  centralHi := (21633642560179687701/12500000000000000000)
  directionLo := (22517009081064758099/12500000000000000000)
  directionHi := (180136072648518064793/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree014.table
  base := (-2183226171349603528885048294344545767/80000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-2792733707675697078579024678901000000000000)
      constant := (10129537701423383485459679285283471470672125) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree014.table
  base := (-292376454477086791056513485259380890857/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-122124177801349135569338042031983956000000000000)
      constant := (443307282229049559123332101933021750866294339727) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree014.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel014

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22517009081064758099/12500000000000000000)
  centralHi := (180136072648518064793/100000000000000000000)
  directionLo := (46734009264854972909/25000000000000000000)
  directionHi := (186936037059419891637/100000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree015.table
  base := (-1629876324345875274567188812163978331113/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-2991720520630409858239828828651000000000000)
      constant := (11401942564750468701048877220321787662041903) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree015.table
  base := (-20592468078152249131440575913672019929/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-130825747686335873889125032742421518500000000000)
      constant := (499046822442028605281430911952572961956572865520) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree015.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel015

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46734009264854972909/25000000000000000000)
  centralHi := (186936037059419891637/100000000000000000000)
  directionLo := (48374295365494366681/25000000000000000000)
  directionHi := (7739887258479098669/4000000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree016.table
  base := (-2786339319150046887114928923019574929069/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-3190707333585122637900632978401000000000000)
      constant := (12811553703857596173487852110725691836987339) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree016.table
  base := (-700517112022932644842610072187559414329/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-139527317571322612208912023452859081000000000000)
      constant := (560788491060035510001595091786943467842541786876) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree016.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel016

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48374295365494366681/25000000000000000000)
  centralHi := (7739887258479098669/4000000000000000000)
  directionLo := (390318417364746481/195312500000000000)
  directionHi := (199843029690750198273/100000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree017.table
  base := (-3769719106676178120464772885520616930571/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-3389694146539835417561437128151000000000000)
      constant := (14353735980951967182527458220264015738733501) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree017.table
  base := (-1891901116966723616206085003871403344479/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-148228887456309350528699014163296643500000000000)
      constant := (628329924546125228719228279770514017427941726738) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree017.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel017

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (390318417364746481/195312500000000000)
  centralHi := (199843029690750198273/100000000000000000000)
  directionLo := (205993479989602327141/100000000000000000000)
  directionHi := (102996739994801163571/50000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree018.table
  base := (-4602460322264157627735084351852529567199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-3588680959494548197222241277901000000000000)
      constant := (16024696252661140545790692091717422503143369) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree018.table
  base := (-2307517641593148913109609579265714494273/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-156930457341296088848486004873734206000000000000)
      constant := (701505494812454092728359537431623550846873447406) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree018.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel018

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205993479989602327141/100000000000000000000)
  centralHi := (102996739994801163571/50000000000000000000)
  directionLo := (211965542200791030949/100000000000000000000)
  directionHi := (4239310844015820619/2000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree019.table
  base := (-2651583206655565035642470505438659405091/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-3787667772449260976883045427651000000000000)
      constant := (17821290536374998815338869595668233121079242) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree019.table
  base := (-1328591199095404920897746943178474800619/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 204490000000000000000000000000000000000000000
      center := (1758614)
      previous := (879307)
      next := (879307)
      square := (23185648650204681659736661300500000000000000)
      linear := (-458814479851198967225132951756708500000000000)
      constant := (2161157661134484550202387713546854115833568276) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree019.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel019

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (211965542200791030949/100000000000000000000)
  centralHi := (4239310844015820619/2000000000000000000)
  directionLo := (10888694637412231211/5000000000000000000)
  directionHi := (217773892748244624221/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree020.table
  base := (-735921916007264970148238862831876485213/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-3986654585403973756543849577401000000000000)
      constant := (19740892918840808882769895733346302991992024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree020.table
  base := (-184291332024210020343765945694187018333/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-174333597111269565488059986294609331000000000000)
      constant := (864232529609108274158273285118002461236677195616) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree020.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel020

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10888694637412231211/5000000000000000000)
  centralHi := (217773892748244624221/100000000000000000000)
  directionLo := (223431299609013109301/100000000000000000000)
  directionHi := (111715649804506554651/50000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree021.table
  base := (-254724928382938890012663071035039974537/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-4185641398358686536204653727151000000000000)
      constant := (21781300291880020349647290020222956107581175) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree021.table
  base := (-6376938337793805967706606817642164902031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-183035166996256303807846977005046893500000000000)
      constant := (953573151189981457147518594332304401181155877241) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree021.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel021

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223431299609013109301/100000000000000000000)
  centralHi := (111715649804506554651/50000000000000000000)
  directionLo := (228948952666792539511/100000000000000000000)
  directionHi := (28618619083349067439/12500000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree022.table
  base := (-3378187990399348776411695177586073482181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-4384628211313399315865457876901000000000000)
      constant := (23940659414515518023580302114835407163022822) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree022.table
  base := (-3382085357744298502783792411664783943401/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (5246774)
      previous := (2623387)
      next := (2623387)
      square := (69173712088627190736900287020500000000000000)
      linear := (-1584601131249942496922594774508136000000000000)
      constant := (8662139518367851272715188196139095580294096782) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree022.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel022

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (228948952666792539511/100000000000000000000)
  centralHi := (28618619083349067439/12500000000000000000)
  directionLo := (117168361994044535429/50000000000000000000)
  directionHi := (234336723988089070859/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree023.table
  base := (-7061372172867066390611556124317317904363/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-4583615024268112095526262026651000000000000)
      constant := (26217408974985779152566952459425873274162653) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree023.table
  base := (-883531338550770831832555869398233470167/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-200438306766229780447420958425922018500000000000)
      constant := (1147801577508200823947295166712777582284211889096) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree023.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel023

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117168361994044535429/50000000000000000000)
  centralHi := (234336723988089070859/100000000000000000000)
  directionLo := (239603375376304890757/100000000000000000000)
  directionHi := (119801687688152445379/50000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree024.table
  base := (-227840684039834148634670218194486329679/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-4782601837222824875187066176401000000000000)
      constant := (28610232445799960471853046034078217929095968) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree024.table
  base := (-3648480301925582175280765346958902625103/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-209139876651216518767207949136359581000000000000)
      constant := (1252563789009547424746566489695532509458312039666) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree024.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel024

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (239603375376304890757/100000000000000000000)
  centralHi := (119801687688152445379/50000000000000000000)
  directionLo := (122378362848551681721/50000000000000000000)
  directionHi := (244756725697103363443/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree025.table
  base := (-7451537232031210563841745224790956539347/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-4981588650177537654847870326151000000000000)
      constant := (31118019141718433849985311530785328344850357) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree025.table
  base := (-3728432326671385935746784286136849688419/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-217841446536203257086994939846797143500000000000)
      constant := (1362357058337616821302333267301151841106562345418) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree025.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel025

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122378362848551681721/50000000000000000000)
  centralHi := (244756725697103363443/100000000000000000000)
  directionLo := (390318417364746481/156250000000000000)
  directionHi := (249803787113437747841/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree026.table
  base := (-7548824363994569092788016778257760778877/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (86)
      previous := (43)
      next := (43)
      square := (1133827994043947462454724500000000000000)
      linear := (-30654292681255919730820559029000000000000)
      constant := (199643974918450922240915989988242239221123) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree026.table
  base := (-3776750653140979713556345056294642047807/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (3756566)
      previous := (1878283)
      next := (1878283)
      square := (49526740607833669107484820884500000000000000)
      linear := (-1340491221427159736134804322823874000000000000)
      constant := (8740476332343248845210445514794234918919484866) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree026.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel026

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (390318417364746481/156250000000000000)
  centralHi := (249803787113437747841/100000000000000000000)
  directionLo := (254750877012159383247/100000000000000000000)
  directionHi := (15921929813259961453/6250000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree027.table
  base := (-7587444453304027363014904730227752577493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-5379562276086963214169478625651000000000000)
      constant := (36474879186883741723684055683956009814403683) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree027.table
  base := (-7591544287254975840321105581626559506617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-235244586306176733726568921267672268500000000000)
      constant := (1596879612643866948374453209306803263473982217087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree027.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel027

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (254750877012159383247/100000000000000000000)
  centralHi := (15921929813259961453/6250000000000000000)
  directionLo := (25960371072215625241/10000000000000000000)
  directionHi := (259603710722156252411/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree028.table
  base := (-94641862053449854190754108507090833499/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-5578549089041675993830282775401000000000000)
      constant := (39322493621245569344528363246237131931093520) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree028.table
  base := (-59179202987339707418605762589405471597/78125000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-243946156191163472046355911978109831000000000000)
      constant := (1721545277961819560693397177568715352002748654976) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree028.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel028

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (25960371072215625241/10000000000000000000)
  centralHi := (259603710722156252411/100000000000000000000)
  directionLo := (132183739452855560237/50000000000000000000)
  directionHi := (10574699156228444819/4000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree029.table
  base := (-7503873590690933234871292205272513756401/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-5777535901996388773491086925151000000000000)
      constant := (42282111332054787394164081390512945175168231) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree029.table
  base := (-234594107359997681665768248173282596461/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-252647726076150210366142902688547393500000000000)
      constant := (1851112920821774645582093165729746568815387015072) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree029.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel029

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (132183739452855560237/50000000000000000000)
  centralHi := (10574699156228444819/4000000000000000000)
  directionLo := (269046912610440938569/100000000000000000000)
  directionHi := (26904691261044093857/10000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree030.table
  base := (-7387834304056977760068154399313380089693/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-5976522714951101553151891074901000000000000)
      constant := (45353256420126524319591969429733538764841883) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree030.table
  base := (-3695287216470015335498396105153574097989/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-261349295961136948685929893398984956000000000000)
      constant := (1985561799131462407327375323040656899368600961958) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree030.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel030

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (269046912610440938569/100000000000000000000)
  centralHi := (26904691261044093857/10000000000000000000)
  directionLo := (273646338304496361141/100000000000000000000)
  directionHi := (136823169152248180571/50000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree031.table
  base := (-7225608373596686570723351803298711488711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-6175509527905814332812695224651000000000000)
      constant := (48535527126962166693293585588536017758407841) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree031.table
  base := (-28911994155735549046881302946919552857/40000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-270050865846123687005716884109422518500000000000)
      constant := (2124874405792194650348664383348055370132980431750) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree031.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel031

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (273646338304496361141/100000000000000000000)
  centralHi := (136823169152248180571/50000000000000000000)
  directionLo := (278169724718035232653/100000000000000000000)
  directionHi := (139084862359017616327/50000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree032.table
  base := (-7019202733306142143447042365493669619331/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-6374496340860527112473499374401000000000000)
      constant := (51828584280716376576721813173663569834333061) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree032.table
  base := (-351064273143910027774547334044577472661/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-278752435731110425325503874819860081000000000000)
      constant := (2269035964007200404030561658983411824588428623420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree032.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel032

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (278169724718035232653/100000000000000000000)
  centralHi := (139084862359017616327/50000000000000000000)
  directionLo := (141310361467194020633/50000000000000000000)
  directionHi := (282620722934388041267/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree033.table
  base := (-3385155841869710259711681070466938737737/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-6573483153815239892134303524151000000000000)
      constant := (55232141544595515118916533191815174706644894) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree033.table
  base := (-3386062374803262266172988295168057772831/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (5246774)
      previous := (2623387)
      next := (2623387)
      square := (69173712088627190736900287020500000000000000)
      linear := (-2375652938976009616903230293638823500000000000)
      constant := (19983752077736767625670474536868916067299707042) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree033.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel033

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141310361467194020633/50000000000000000000)
  centralHi := (282620722934388041267/100000000000000000000)
  directionLo := (287002700883118449539/100000000000000000000)
  directionHi := (14350135044155922477/5000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree034.table
  base := (-3240182798980538067324744176556718630393/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-6772469966769952671795107673901000000000000)
      constant := (58745957185551672620194222692220329102927166) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree034.table
  base := (-3240971232987191975850788251276122337143/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-296155575501083901965077856240735206000000000000)
      constant := (2571857990636592652459647974464162817602144736546) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree034.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel034

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287002700883118449539/100000000000000000000)
  centralHi := (14350135044155922477/5000000000000000000)
  directionLo := (291318773161726377499/100000000000000000000)
  directionHi := (116527509264690551/40000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree035.table
  base := (-3075286018442602230968342922815923301897/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-6971456779724665451455911823651000000000000)
      constant := (62369827125790366945649777916310717923958814) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree035.table
  base := (-153798557288300190707187446758269110829/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-304857145386070640284864846951172768500000000000)
      constant := (2730499046028964444210423789320102557282003328760) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree035.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel035

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (291318773161726377499/100000000000000000000)
  centralHi := (116527509264690551/40000000000000000)
  directionLo := (9236619591772059077/3125000000000000000)
  directionHi := (59114365387341178093/20000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree036.table
  base := (-1156390091660175865690212626372339727291/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-7170443592679378231116715973401000000000000)
      constant := (66103579076945244618492126525326372930439105) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree036.table
  base := (-5783140199687526475507495697443233412253/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-313558715271057378604651837661610331000000000000)
      constant := (2893949667577143802232057051156921082002974663483) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree036.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel036

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (9236619591772059077/3125000000000000000)
  centralHi := (59114365387341178093/20000000000000000000)
  directionLo := (299764544536125297409/100000000000000000000)
  directionHi := (29976454453612529741/10000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree037.table
  base := (-1343840379605169574543341211623572150183/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-7369430405634091010777520123151000000000000)
      constant := (69947067588116380030408522676004465226476292) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree037.table
  base := (-537639372977574806324290828441018769589/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-322260285156044116924438828372047893500000000000)
      constant := (3062203524849440176245810001201067048062860085790) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree037.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel037

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (299764544536125297409/100000000000000000000)
  centralHi := (29976454453612529741/10000000000000000000)
  directionLo := (303899423236042479951/100000000000000000000)
  directionHi := (18993713952252654997/6250000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree038.table
  base := (-2465765904361140574549086886202792133363/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-7568417218588803790438324272901000000000000)
      constant := (73900169865344045298917881878038956258923306) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree038.table
  base := (-986485338794976275485453622337658040361/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 204490000000000000000000000000000000000000000
      center := (1758614)
      previous := (879307)
      next := (879307)
      square := (23185648650204681659736661300500000000000000)
      linear := (-916791842218922036687606147042896000000000000)
      constant := (8961925968420871866085655275893126341163289555) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree038.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel038

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303899423236042479951/100000000000000000000)
  centralHi := (18993713952252654997/6250000000000000000)
  directionLo := (38497349081918920051/12500000000000000000)
  directionHi := (307978792655351360409/100000000000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree039.table
  base := (-4451074739343054688220797890097415868853/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (86)
      previous := (43)
      next := (43)
      square := (1133827994043947462454724500000000000000)
      linear := (-45960970600849210473959339779000000000000)
      constant := (461318238120207251086615367353402584131147) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree039.table
  base := (-4451850031181607563256213759352389524799/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (3756566)
      previous := (1878283)
      next := (1878283)
      square := (49526740607833669107484820884500000000000000)
      linear := (-2009842751041524222272265146703686500000000000)
      constant := (20195860395404252322171216478911417788792254881) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree039.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel039

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (38497349081918920051/12500000000000000000)
  centralHi := (307978792655351360409/100000000000000000000)
  directionLo := (39000603762893957869/12500000000000000000)
  directionHi := (312004830103151662953/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree040.table
  base := (-983627042345576656201774678112311139529/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-7966390844498229349759932572401000000000000)
      constant := (82134817200841537431702937694386077669678396) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree040.table
  base := (-1967589704398762347962453820294125601551/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-348364994811004331883799800503360581000000000000)
      constant := (3595735114816938876882532710913307944764343959922) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree040.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel040

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39000603762893957869/12500000000000000000)
  centralHi := (312004830103151662953/100000000000000000000)
  directionLo := (315979574165712748241/100000000000000000000)
  directionHi := (157989787082856374121/50000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree041.table
  base := (-169113464544718673158421918186758473027/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-8165377657452942129420736722151000000000000)
      constant := (86416200855466398423884083514019756361168740) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree041.table
  base := (-3382850079613210474805849194152181500711/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-357066564695991070203586791213798143500000000000)
      constant := (3783156185505957904025529897519904522383222834721) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree041.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel041

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (315979574165712748241/100000000000000000000)
  centralHi := (157989787082856374121/50000000000000000000)
  directionLo := (19994058548357109409/6250000000000000000)
  directionHi := (63980987354742750109/20000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree042.table
  base := (-1397363597193977049756641824925781868169/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-8364364470407654909081540871901000000000000)
      constant := (90806870829893638296722203651429585728558878) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree042.table
  base := (-2795229421858919788586601910240057938257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-365768134580977808523373781924235706000000000000)
      constant := (3975360906871583319794950457878042743872130321127) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree042.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel042

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (19994058548357109409/6250000000000000000)
  centralHi := (63980987354742750109/20000000000000000000)
  directionLo := (161891356976246898543/50000000000000000000)
  directionHi := (323782713952493797087/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree043.table
  base := (-543048369248444458486521214567234640961/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-8563351283362367688742345021651000000000000)
      constant := (95306774464208163798499646008033049382710364) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree043.table
  base := (-135789220232791608729143432127566474889/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-374469704465964546843160772634673268500000000000)
      constant := (4172346989815198598557717907263083917878875190064) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree043.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel043

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (161891356976246898543/50000000000000000000)
  centralHi := (323782713952493797087/100000000000000000000)
  directionLo := (163807297713419235243/50000000000000000000)
  directionHi := (327614595426838470487/100000000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree044.table
  base := (-757465599099272256702199480284188701769/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-8762338096317080468403149171401000000000000)
      constant := (99915867301356722655083963455632944218802078) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree044.table
  base := (-1515306117304244313197037180600659257237/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (5246774)
      previous := (2623387)
      next := (2623387)
      square := (69173712088627190736900287020500000000000000)
      linear := (-3166704746702076736883865812769511000000000000)
      constant := (36149690100885894066145427261847468379375227867) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree044.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel044

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163807297713419235243/50000000000000000000)
  centralHi := (327614595426838470487/100000000000000000000)
  directionLo := (331402173226036161943/100000000000000000000)
  directionHi := (41425271653254520243/12500000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree045.table
  base := (-411581220273180386450767257796085597089/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-8961324909271793248063953321151000000000000)
      constant := (104634111809389360845157906847784923068183918) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree045.table
  base := (-411743059679860347269413504622799903303/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-391872844235938023482734754055548393500000000000)
      constant := (4580655813220367913110457827653943267259876720066) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree045.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel045

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (331402173226036161943/100000000000000000000)
  centralHi := (41425271653254520243/12500000000000000000)
  directionLo := (20946684338344978997/6250000000000000000)
  directionHi := (335146949413519663953/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree046.table
  base := (-48537346306131606578624133099707925819/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-9160311722226506027724757470901000000000000)
      constant := (109461476302736897183199837294945798721073178) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree046.table
  base := (-486769980813199575891674666344107379/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-400574414120924761802521744765985956000000000000)
      constant := (4791975546344110748288358889983836779628033053800) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree046.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel046

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (20946684338344978997/6250000000000000000)
  centralHi := (335146949413519663953/100000000000000000000)
  directionLo := (67770068609508412597/20000000000000000000)
  directionHi := (169425171523771031493/50000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree047.table
  base := (663173762297642376839662665263296046573/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-9359298535181218807385561620651000000000000)
      constant := (114397934031520599790870648083438997031870837) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree047.table
  base := (132586572842353049634772750943952265829/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-409275984005911500122308735476423518500000000000)
      constant := (5008070539725642780483905291621976780581131683905) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree047.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel047

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67770068609508412597/20000000000000000000)
  centralHi := (169425171523771031493/50000000000000000000)
  directionLo := (342513696464368511801/100000000000000000000)
  directionHi := (171256848232184255901/50000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree048.table
  base := (22772645263153123242831872131438921691/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-9558285348135931587046365770401000000000000)
      constant := (119443462412719745685656734233121643377009856) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree048.table
  base := (291448323471486702496928845909812929621/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-417977553890898238442095726186861081000000000000)
      constant := (5228939812695735313166292315160840888099064791345) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree048.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel048

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (342513696464368511801/100000000000000000000)
  centralHi := (171256848232184255901/50000000000000000000)
  directionLo := (173069140481437501607/50000000000000000000)
  directionHi := (69227656192575000643/20000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree049.table
  base := (1142819549491141299171553941988218373209/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-9757272161090644366707169920151000000000000)
      constant := (124598042381099925251775956317741017810144642) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree049.table
  base := (2285460135134274272272965055323000995901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-426679123775884976761882716897298643500000000000)
      constant := (5454582537514478793017795024907956389614454817189) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree049.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel049

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (173069140481437501607/50000000000000000000)
  centralHi := (69227656192575000643/20000000000000000000)
  directionLo := (349725301958812846977/100000000000000000000)
  directionHi := (174862650979406423489/50000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree050.table
  base := (3147647929582299343868408962689170145901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-9956258974045357146367974069901000000000000)
      constant := (129861657841247020782279625351306969754657269) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree050.table
  base := (786873443779643266695889714192058341687/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-435380693660871715081669707607736206000000000000)
      constant := (5684998015523078184178531029880259112023603376572) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree050.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel050

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (349725301958812846977/100000000000000000000)
  centralHi := (174862650979406423489/50000000000000000000)
  directionLo := (353275903667985051583/100000000000000000000)
  directionHi := (5519935994812266431/1562500000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree051.table
  base := (2021697692535862121510106251922260939511/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-10155245787000069926028778219651000000000000)
      constant := (135234295204957681003262360071088224197554718) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree051.table
  base := (505407831729057141945529224526968867667/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-444082263545858453401456698318173768500000000000)
      constant := (5920185657014590200400166569687002864916401130904) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree051.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel051

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (353275903667985051583/100000000000000000000)
  centralHi := (5519935994812266431/1562500000000000000)
  directionLo := (178395586684957037857/50000000000000000000)
  directionHi := (71358234673982815143/20000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree052.table
  base := (4972813586506466188640856058270059247081/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (86)
      previous := (43)
      next := (43)
      square := (1133827994043947462454724500000000000000)
      linear := (-61267648520442501217098120529000000000000)
      constant := (832638715980416298920795949841270059247081) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree052.table
  base := (4972699345192103978362927500578605360717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (3756566)
      previous := (1878283)
      next := (1878283)
      square := (49526740607833669107484820884500000000000000)
      linear := (-2679194280655888708409725970583499000000000000)
      constant := (36450561918601557056364724245304784560761479277) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree052.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel052

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (178395586684957037857/50000000000000000000)
  centralHi := (71358234673982815143/20000000000000000000)
  directionLo := (22517009081064758099/6250000000000000000)
  directionHi := (72054429059407225917/20000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree053.table
  base := (1187169045720504984886658406776290552153/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-10553219412909495485350386519151000000000000)
      constant := (146306591543852045282021890664503965516569285) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree053.table
  base := (1187149387573044559124196089446652733979/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-461485403315831930041030679739048893500000000000)
      constant := (6404875517085776931298723327872071855812256510655) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree053.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel053

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22517009081064758099/6250000000000000000)
  centralHi := (72054429059407225917/20000000000000000000)
  directionLo := (363719804188852687863/100000000000000000000)
  directionHi := (45464975523606585983/12500000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree054.table
  base := (6932441932671650767675652499585599419293/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-10752206225864208265011190668901000000000000)
      constant := (152006232658444439100104489814721466301860517) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree054.table
  base := (6932357395568763556562740508445656780101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-470186973200818668360817670449486456000000000000)
      constant := (6654376960932814862200782757893720393701659010989) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree054.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel054

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (363719804188852687863/100000000000000000000)
  centralHi := (45464975523606585983/12500000000000000000)
  directionLo := (367135088545655045163/100000000000000000000)
  directionHi := (91783772136413761291/25000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree055.table
  base := (995320357014999271802527484129871651887/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-10951193038818921044671994818651000000000000)
      constant := (157814859442069175398935148702411086473351224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree055.table
  base := (3981245086532863853462239781687247661587/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (5246774)
      previous := (2623387)
      next := (2623387)
      square := (69173712088627190736900287020500000000000000)
      linear := (-3957756554428143856864501331900198500000000000)
      constant := (57096272698150651948854301793897529350796522566) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree055.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel055

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (367135088545655045163/100000000000000000000)
  centralHi := (91783772136413761291/25000000000000000000)
  directionLo := (92629723403072204489/25000000000000000000)
  directionHi := (370518893612288817957/100000000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree056.table
  base := (9026173518545038112429485269194504943013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-11150179851773633824332798968401000000000000)
      constant := (163732466067538228800065728325999871335369197) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree056.table
  base := (564131940499176622136238442105074259007/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-487590112970792145000391651870361581000000000000)
      constant := (7167691371083443117706309814629652437005579609968) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree056.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel056

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (92629723403072204489/25000000000000000000)
  centralHi := (370518893612288817957/100000000000000000000)
  directionLo := (373872074118839783273/100000000000000000000)
  directionHi := (186936037059419891637/50000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree057.table
  base := (10123244810691384699681562825264011352619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-11349166664728346603993603118151000000000000)
      constant := (169759047615387437061434529974676617918592611) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree057.table
  base := (1012319113482079665953581432243766067539/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 204490000000000000000000000000000000000000000
      center := (1758614)
      previous := (879307)
      next := (879307)
      square := (23185648650204681659736661300500000000000000)
      linear := (-1374769204586645106150079342329083500000000000)
      constant := (20585883300606766243672424844073406363776050110) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree057.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel057

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (373872074118839783273/100000000000000000000)
  centralHi := (186936037059419891637/50000000000000000000)
  directionLo := (377195446802015171921/100000000000000000000)
  directionHi := (188597723401007585961/50000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree058.table
  base := (11253752157781538839356028394145786612783/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-11548153477683059383654407267901000000000000)
      constant := (175894599932479403511678901967581137937560327) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree058.table
  base := (5626853026332804816688799535398564728791/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-504993252740765621639965633291236706000000000000)
      constant := (7700086317801038687449253272420812619537892048798) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree058.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel058

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (377195446802015171921/100000000000000000000)
  centralHi := (188597723401007585961/50000000000000000000)
  directionLo := (76097958545658893823/20000000000000000000)
  directionHi := (95122448182073617279/25000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree059.table
  base := (2483534962634949241326604675365385217927/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-11747140290637772163315211417651000000000000)
      constant := (182139119512631840669904288201480250509148315) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree059.table
  base := (194025550355667884050398605125416451523/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-513694822625752359959752624001674268500000000000)
      constant := (7973438558015204431819914299354186053576871179008) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree059.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel059

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76097958545658893823/20000000000000000000)
  centralHi := (95122448182073617279/25000000000000000000)
  directionLo := (2398474121484821719/625000000000000000)
  directionHi := (383755859437571475041/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree060.table
  base := (13614995262052722428393149841016878267107/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-11946127103592484942976015567401000000000000)
      constant := (188492603395840458477053510425816852427141083) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree060.table
  base := (3403740318893970271358325313465165042269/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-522396392510739098279539614712111831000000000000)
      constant := (8251560463938076841066439209961303971966874079764) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree060.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel060

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2398474121484821719/625000000000000000)
  centralHi := (383755859437571475041/100000000000000000000)
  directionLo := (386994362923954933449/100000000000000000000)
  directionHi := (7739887258479098669/2000000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree061.table
  base := (92785616987458826389105697128037925013/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-12145113916547197722636819717151000000000000)
      constant := (194955049083199929590404433774978145492351520) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree061.table
  base := (14845669550331395095742500090858897416511/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-531097962395725836599326605422549393500000000000)
      constant := (8534451927342520213552986967583262808561179271479) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree061.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel061

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (386994362923954933449/100000000000000000000)
  centralHi := (7739887258479098669/2000000000000000000)
  directionLo := (97551497367149102973/25000000000000000000)
  directionHi := (390205989468596411893/100000000000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree062.table
  base := (2013721587245453683947529668279033811803/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-12344100729501910502297623866901000000000000)
      constant := (201526454465077645556244210228162753713557656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree062.table
  base := (3221949534520390642574656508574784615499/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-539799532280712574919113596132986956000000000000)
      constant := (8822112856879410650108165548408704192624721987055) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree062.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel062

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (97551497367149102973/25000000000000000000)
  centralHi := (390205989468596411893/100000000000000000000)
  directionLo := (393391397337835799031/100000000000000000000)
  directionHi := (49173924667229474879/12500000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree063.table
  base := (17407206663515282030928905449369174553831/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-12543087542456623281958428016651000000000000)
      constant := (208206817760475878801994456299668890499597439) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree063.table
  base := (4351796299440744887679936493952811304487/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-548501102165699313238900586843424518500000000000)
      constant := (9114543175445599959953487315767408150290341533372) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree063.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel063

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (393391397337835799031/100000000000000000000)
  centralHi := (49173924667229474879/12500000000000000000)
  directionLo := (396551218358566680711/100000000000000000000)
  directionHi := (49568902294820835089/12500000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree064.table
  base := (1873799171787265658858379841073984699973/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-12742074355411336061619232166401000000000000)
      constant := (214996137465839533777974641142279034142954370) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree064.table
  base := (4684493327512405100350353215306947552263/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-557202672050686051558687577553862081000000000000)
      constant := (9411742817962327389945398583181907880596550469628) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree064.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel064

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (396551218358566680711/100000000000000000000)
  centralHi := (49568902294820835089/12500000000000000000)
  directionLo := (79937211876300079309/20000000000000000000)
  directionHi := (199843029690750198273/50000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree065.table
  base := (20102120350204616834760343149478938276047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (86)
      previous := (43)
      next := (43)
      square := (1133827994043947462454724500000000000000)
      linear := (-76574326440035791960236901279000000000000)
      constant := (1312984688235728689040421135534478938276047) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree065.table
  base := (2512763071067966004219484446365904396661/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (3756566)
      previous := (1878283)
      next := (1878283)
      square := (49526740607833669107484820884500000000000000)
      linear := (-3348545810270253194547186794463311500000000000)
      constant := (57477584198225283620220771503470882950229393128) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree065.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel065

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79937211876300079309/20000000000000000000)
  centralHi := (199843029690750198273/50000000000000000000)
  directionLo := (402796503641926974249/100000000000000000000)
  directionHi := (1611186014567707897/400000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree066.table
  base := (21499586219731721519004934129997942048911/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-13140047981320761620940840465901000000000000)
      constant := (228901641226879997240237389253298152206265959) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree066.table
  base := (10749786346386239086141466443506184295167/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (5246774)
      previous := (2623387)
      next := (2623387)
      square := (69173712088627190736900287020500000000000000)
      linear := (-4748808362154210976845136851030886000000000000)
      constant := (82813635237155596980877022426223112032827687006) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree066.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel066

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (402796503641926974249/100000000000000000000)
  centralHi := (1611186014567707897/400000000000000000)
  directionLo := (405883112026614774883/100000000000000000000)
  directionHi := (101470778006653693721/25000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree067.table
  base := (22930383973463175039447630538136267577881/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-13339034794275474400601644615651000000000000)
      constant := (236017823306309635698477273188599529220661889) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree067.table
  base := (22930372381741480830493698100889106009777/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-583307381705646266518048549685174768500000000000)
      constant := (10331957181417177923170856812447401296460233684153) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree067.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel067

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (405883112026614774883/100000000000000000000)
  centralHi := (101470778006653693721/25000000000000000000)
  directionLo := (408946424254642613437/100000000000000000000)
  directionHi := (204473212127321306719/50000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree068.table
  base := (4878901818465017567478030457506201248881/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-13538021607230187180262448765401000000000000)
      constant := (243242957786403576487130814376635740055304445) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree068.table
  base := (24394499161188521235792142237595460893493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-592008951590633004837835540395612331000000000000)
      constant := (10648233649634723118483103033770045283811784846877) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree068.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel068

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (408946424254642613437/100000000000000000000)
  centralHi := (204473212127321306719/50000000000000000000)
  directionLo := (205993479989602327141/50000000000000000000)
  directionHi := (411986959979204654283/100000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree069.table
  base := (12945978880628763601052831584820463651247/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-13737008420184899959923252915151000000000000)
      constant := (250577044022416690978085177498163316714121486) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree069.table
  base := (3236493656832141157304274874260537546709/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-600710521475619743157622531106049893500000000000)
      constant := (10969279240470325053499246132869933612001804960808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree069.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel069

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (205993479989602327141/50000000000000000000)
  centralHi := (411986959979204654283/100000000000000000000)
  directionLo := (415005219816757734419/100000000000000000000)
  directionHi := (20750260990837886721/5000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree070.table
  base := (5484545351909346792429031075930927156399/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-13935995233139612739584057064901000000000000)
      constant := (258020081470048353871365480234169133447157155) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree070.table
  base := (13711359737337723458898968640758395157521/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-609412091360606481477409521816487456000000000000)
      constant := (11295093930393782787610974739097391100787478082738) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree070.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel070

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (415005219816757734419/100000000000000000000)
  centralHi := (20750260990837886721/5000000000000000000)
  directionLo := (83600337261856554219/20000000000000000000)
  directionHi := (52250210788660346387/12500000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree071.table
  base := (3623351671030058319855890902312477323121/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-14134982046094325519244861214651000000000000)
      constant := (265572069669795636343557928797509969340859592) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree071.table
  base := (3623350891363139517705407328583670818209/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-618113661245593219797196512526925018500000000000)
      constant := (11625677699544779121415144016169081460554398268808) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree071.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel071

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (83600337261856554219/20000000000000000000)
  centralHi := (52250210788660346387/12500000000000000000)
  directionLo := (52622103103112221451/12500000000000000000)
  directionHi := (420976824824897771609/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree072.table
  base := (30584215291985426602397673259533864535697/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-14333968859049038298905665364401000000000000)
      constant := (273233008233743830966783973171083223106532793) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree072.table
  base := (30584209952613831680113924366032366339949/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-626815231130579958116983503237362581000000000000)
      constant := (11961030531160566082382147973021442774702107773461) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree072.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel072

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (52622103103112221451/12500000000000000000)
  centralHi := (420976824824897771609/100000000000000000000)
  directionLo := (423931084401582061899/100000000000000000000)
  directionHi := (4239310844015820619/1000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree073.table
  base := (16107465296520115442986035357188865160607/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-14532955672003751078566469514151000000000000)
      constant := (281002896834414643979090235203652836424285166) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree073.table
  base := (32214926023237883144276264681401811984169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-635516801015566696436770493947800143500000000000)
      constant := (12301152411092899786250653644004171993594027149041) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree073.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel073

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (423931084401582061899/100000000000000000000)
  centralHi := (4239310844015820619/1000000000000000000)
  directionLo := (426864898538343069127/100000000000000000000)
  directionHi := (53358112317292883641/12500000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree074.table
  base := (6775791527113467499371657908065732145441/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-14731942484958463858227273663901000000000000)
      constant := (288881735195351530797228381818002043662897645) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree074.table
  base := (33878953725149335136438021018998439206377/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-644218370900553434756557484658237706000000000000)
      constant := (12646043327400306845028646381847495124020064381553) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree074.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel074

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (426864898538343069127/100000000000000000000)
  centralHi := (53358112317292883641/12500000000000000000)
  directionLo := (214889342968886286249/50000000000000000000)
  directionHi := (429778685937772572499/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree075.table
  base := (35576295038602765871882109027659078683699/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-14930929297913176637888077813651000000000000)
      constant := (296869523083171578706021969714186884297545131) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree075.table
  base := (17788145846518250434667231964421877448937/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-652919940785540173076344475368675268500000000000)
      constant := (12995703270003934874112413887190749881765916778786) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree075.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel075

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (214889342968886286249/50000000000000000000)
  centralHi := (429778685937772572499/100000000000000000000)
  directionLo := (216336425601796877009/50000000000000000000)
  directionHi := (432672851203593754019/100000000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree076.table
  base := (7461388327270372692887534311907469989817/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-15129916110867889417548881963401000000000000)
      constant := (304966260300855491425094608954962812141395365) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree076.table
  base := (9326734693638630770308492352423008029019/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 204490000000000000000000000000000000000000000
      center := (1758614)
      previous := (879307)
      next := (879307)
      square := (23185648650204681659736661300500000000000000)
      linear := (-1832746566954368175612552537615271000000000000)
      constant := (36980975707471112405827027749424388364741638124) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree076.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel076

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (216336425601796877009/50000000000000000000)
  centralHi := (432672851203593754019/100000000000000000000)
  directionLo := (10888694637412231211/2500000000000000000)
  directionHi := (435547785496489248441/100000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree077.table
  base := (39070896444669933540329646491439279211829/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-15328902923822602197209686113151000000000000)
      constant := (313171946682082815206367288661405238186799101) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree077.table
  base := (9767723499278084019619223882731394636283/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (5246774)
      previous := (2623387)
      next := (2623387)
      square := (69173712088627190736900287020500000000000000)
      linear := (-5539860169880278096825772370161573500000000000)
      constant := (113300249598346802897906062483156251637084958188) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree077.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel077

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10888694637412231211/2500000000000000000)
  centralHi := (435547785496489248441/100000000000000000000)
  directionLo := (438403867151219868429/100000000000000000000)
  directionHi := (43840386715121986843/10000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree078.table
  base := (1021703965819107532439723120705002516671/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (86)
      previous := (43)
      next := (43)
      square := (1133827994043947462454724500000000000000)
      linear := (-91881004359629082703375682029000000000000)
      constant := (1902287467967157325492942185877700100666840) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree078.table
  base := (4086815653983907908254823400002257945823/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (3756566)
      previous := (1878283)
      next := (1878283)
      square := (49526740607833669107484820884500000000000000)
      linear := (-4017897339884617680684647618343124000000000000)
      constant := (83273947792620519756023884242004275480814944630) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree078.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel078

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438403867151219868429/100000000000000000000)
  centralHi := (43840386715121986843/10000000000000000000)
  directionLo := (110310365564447599501/25000000000000000000)
  directionHi := (88248292451558079601/20000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree079.table
  base := (21349363749652234062245862688053742308603/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-15726876549732027756531294412651000000000000)
      constant := (329910166395430955565533112189003664900307814) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree079.table
  base := (4269872570992225736823763027018125147863/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-687726220325487126355492438210425518500000000000)
      constant := (14442033151941382146494232265866607093937253258070) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree079.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel079

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110310365564447599501/25000000000000000000)
  centralHi := (88248292451558079601/20000000000000000000)
  directionLo := (55507615651148730649/12500000000000000000)
  directionHi := (444060925209189845193/100000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree080.table
  base := (44562602452253699639579639411720940442787/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-15925863362686740536192098562401000000000000)
      constant := (338442699508972709767578465914160838934831003) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree080.table
  base := (11140650230658975820711415501136069289987/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-696427790210473864675279428920863081000000000000)
      constant := (14815538122049006940001872821426291363435403371372) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree080.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel080

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55507615651148730649/12500000000000000000)
  centralHi := (444060925209189845193/100000000000000000000)
  directionLo := (223431299609013109301/50000000000000000000)
  directionHi := (446862599218026218603/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree081.table
  base := (23229891495921176795648509731783139743269/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-16124850175641453315852902712151000000000000)
      constant := (347084181342613781073930386166123701233224922) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree081.table
  base := (23229890842241651508886005444771269449431/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-705129360095460602995066419631300643500000000000)
      constant := (15193812083632705556748341588358678230952986282718) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree081.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel081

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (223431299609013109301/50000000000000000000)
  centralHi := (446862599218026218603/100000000000000000000)
  directionLo := (449646816804187946113/100000000000000000000)
  directionHi := (224823408402093973057/50000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree082.table
  base := (12097567174048388227169371958850697066901/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-16323836988596166095513706861901000000000000)
      constant := (355834611825056977259595555114227571217225076) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree082.table
  base := (48390267578968589951737895080727199915321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-713830929980447341314853410341738206000000000000)
      constant := (15576855033617868441203229305276462227433192085569) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree082.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel082

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (449646816804187946113/100000000000000000000)
  centralHi := (224823408402093973057/50000000000000000000)
  directionLo := (452413900255493459123/100000000000000000000)
  directionHi := (113103475063873364781/25000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree083.table
  base := (50354059209188042501251653597009140211939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-16522823801550878875174511011651000000000000)
      constant := (364693990896118144214284645691265044695817691) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree083.table
  base := (25177029127293623419638516843238181651729/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-722532499865434079634640401052175768500000000000)
      constant := (15964666969409657963158469040138691155568085963762) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree083.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel083

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (452413900255493459123/100000000000000000000)
  centralHi := (113103475063873364781/25000000000000000000)
  directionLo := (56895520257891928681/12500000000000000000)
  directionHi := (455164162063135429449/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree084.table
  base := (52351154230219426848291108505654559174321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-16721810614505591654835315161401000000000000)
      constant := (373662318504994801094994556904214620500460249) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree084.table
  base := (26175576707344744627850047523635677514031/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-731234069750420817954427391762613331000000000000)
      constant := (16357247888818179012160190349284280466467751181518) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree084.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel084

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (56895520257891928681/12500000000000000000)
  centralHi := (455164162063135429449/100000000000000000000)
  directionLo := (457897905333585079023/100000000000000000000)
  directionHi := (28618619083349067439/6250000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree085.table
  base := (54381553505545318739274304114038088400353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-16920797427460304434496119311151000000000000)
      constant := (382739594608804484463147147065482436939659657) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree085.table
  base := (54381552808924463414066374942149978823157/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-739935639635407556274214382473050893500000000000)
      constant := (16754597789995319304327209916431411561661285234973) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree085.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel085

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (457897905333585079023/100000000000000000000)
  centralHi := (28618619083349067439/6250000000000000000)
  directionLo := (460615424178493475511/100000000000000000000)
  directionHi := (57576928022311684439/12500000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree086.table
  base := (56445256820985799339767706151341160653617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-17119784240415017214156923460901000000000000)
      constant := (391925819171350788035723148883300156150461273) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree086.table
  base := (5644525622601873739717539348461345878029/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-748637209520394294594001373183488456000000000000)
      constant := (17156716671381439561911313168215240579001432225810) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree086.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel086

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (460615424178493475511/100000000000000000000)
  centralHi := (57576928022311684439/12500000000000000000)
  directionLo := (231658502042004763607/50000000000000000000)
  directionHi := (92663400816801905443/20000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree087.table
  base := (14635565998939828604753447700642173170831/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-17318771053369729993817727610651000000000000)
      constant := (401220992162081629147724540832933609063481756) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree087.table
  base := (58542263487681008218205665422487351356471/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-757338779405381032913788363893926018500000000000)
      constant := (17563604531660377518337818073392028332728364647919) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree087.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel087

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (231658502042004763607/50000000000000000000)
  centralHi := (92663400816801905443/20000000000000000000)
  directionLo := (58250365282603422969/12500000000000000000)
  directionHi := (466002922260827383753/100000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree088.table
  base := (30336287438639412043175033820418672689911/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-17517757866324442773478531760401000000000000)
      constant := (410625113555209798057629362032239511369189918) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree088.table
  base := (60672574443457395526971340528369085801951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 610090000000000000000000000000000000000000000
      center := (5246774)
      previous := (2623387)
      next := (2623387)
      square := (69173712088627190736900287020500000000000000)
      linear := (-6330911977606345216806407889292261000000000000)
      constant := (148555879088607183788977698504482800055691228559) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree088.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel088

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (58250365282603422969/12500000000000000000)
  centralHi := (466002922260827383753/100000000000000000000)
  directionLo := (117168361994044535429/25000000000000000000)
  directionHi := (468673447976178141717/100000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree089.table
  base := (62836189336758623370653464484018753542257/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-17716744679279155553139335910151000000000000)
      constant := (420138183328970510625317813282438169348641433) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree089.table
  base := (62836188966389081084514210861614693392383/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-774741919175354509553362345314801143500000000000)
      constant := (18391687184627493426721950746868071506595908228087) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree089.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel089

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117168361994044535429/25000000000000000000)
  centralHi := (468673447976178141717/100000000000000000000)
  directionLo := (117832210717222815161/25000000000000000000)
  directionHi := (94265768573778252129/20000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree090.table
  base := (32516553632752775851178149250555650237983/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-17915731492233868332800140059901000000000000)
      constant := (429760201464994622714532956185090309780438254) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree090.table
  base := (65033106949347170420948090363882749739707/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-783443489060341247873149336025238706000000000000)
      constant := (18812881975587615049656458111515750845080743907923) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree090.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel090

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (117832210717222815161/25000000000000000000)
  centralHi := (94265768573778252129/20000000000000000000)
  directionLo := (473969361248569122361/100000000000000000000)
  directionHi := (236984680624284561181/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree091.table
  base := (33631664285893990258537889746045450661957/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 10000000000000000000000000000000000000000
      center := (86)
      previous := (43)
      next := (43)
      square := (1133827994043947462454724500000000000000)
      linear := (-107187682279222373446514462779000000000000)
      constant := (2600539455312304669218308279268590901323914) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree091.table
  base := (3363166415096958270132864337547499344083/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 436810000000000000000000000000000000000000000
      center := (3756566)
      previous := (1878283)
      next := (1878283)
      square := (49526740607833669107484820884500000000000000)
      linear := (-4687248869498982166822108442222936500000000000)
      constant := (113839323916772477166361767341696493267602790460) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree091.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel091

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (473969361248569122361/100000000000000000000)
  centralHi := (236984680624284561181/50000000000000000000)
  directionLo := (238297625189921503717/50000000000000000000)
  directionHi := (95319050075968601487/20000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree092.table
  base := (69526853178192575171065516669065869049079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-18313705118143293892121748359401000000000000)
      constant := (449331082764242256220608102273189131869294351) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree092.table
  base := (34763426473948952967521997331782638580573/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-800846628830314724512723317446113831000000000000)
      constant := (19669578483105283237502423036194272260313247113994) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree092.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel092

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (238297625189921503717/50000000000000000000)
  centralHi := (95319050075968601487/20000000000000000000)
  directionLo := (95841350150521956303/20000000000000000000)
  directionHi := (119801687688152445379/25000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree093.table
  base := (71823681019392847450347593976971181372861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-18512691931098006671782552509151000000000000)
      constant := (459279945903342747574512697602176129652013509) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree093.table
  base := (71823680822877740219886668561406028117211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-809548198715301462832510308156551393500000000000)
      constant := (20105080198624813510480829686962231073088379033779) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree093.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel093

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (95841350150521956303/20000000000000000000)
  centralHi := (119801687688152445379/25000000000000000000)
  directionLo := (48180409633908521231/10000000000000000000)
  directionHi := (481804096339085212311/100000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree094.table
  base := (74153812040265351126042573526613248080793/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-18711678744052719451443356658901000000000000)
      constant := (469337757355765100746927260180079138925654017) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree094.table
  base := (74153811872594416380650761494050761345843/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-818249768600288201152297298866988956000000000000)
      constant := (20545350888092408281399363595887893859460272806027) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree094.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel094

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (48180409633908521231/10000000000000000000)
  centralHi := (481804096339085212311/100000000000000000000)
  directionLo := (484387514838451563453/100000000000000000000)
  directionHi := (242193757419225781727/50000000000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree095.table
  base := (9564655774287420680979305198150775595219/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-18910665557007432231104160808651000000000000)
      constant := (479504517113649003931048383686057348604736088) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree095.table
  base := (76517246051255091917168227939415738466737/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 204490000000000000000000000000000000000000000
      center := (1758614)
      previous := (879307)
      next := (879307)
      square := (23185648650204681659736661300500000000000000)
      linear := (-2290723929322091245075025732901458500000000000)
      constant := (58145126180526373161658730570557304701531304913) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree095.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel095

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (484387514838451563453/100000000000000000000)
  centralHi := (242193757419225781727/50000000000000000000)
  directionLo := (486957227909823474923/100000000000000000000)
  directionHi := (121739306977455868731/25000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree096.table
  base := (7891398344225434737413540677936045208953/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-19109652369962145010764964958401000000000000)
      constant := (489780225170362805352847731378007916403130570) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree096.table
  base := (39456991660116608344332414629911496809707/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-835652908370261677791871280287864081000000000000)
      constant := (21440199187572506169456986148681532989144946275846) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree096.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel096

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (486957227909823474923/100000000000000000000)
  centralHi := (121739306977455868731/25000000000000000000)
  directionLo := (122378362848551681721/25000000000000000000)
  directionHi := (97902690278841345377/20000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree097.table
  base := (16268804750205311034586221737512847484463/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-19308639182916857790425769108151000000000000)
      constant := (500164881520311972659614876344695356124371235) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree097.table
  base := (81344023646950100790920495804838000894189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-844354478255248416111658270998301643500000000000)
      constant := (21894776797059365867317562804273225276198607780821) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree097.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel097

namespace ForestUnimodality.Stage80KernelData.Cell112.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (122378362848551681721/25000000000000000000)
  centralHi := (97902690278841345377/20000000000000000000)
  directionLo := (123014098881519730459/25000000000000000000)
  directionHi := (492056395526078921837/100000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 27
  qDenominator := 52
  table := BinomialMassData.Q27_52.Degree098.table
  base := (41903683546346129242424551048425351372973/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1690000000000000000000000000000000000000000
      center := (14534)
      previous := (7267)
      next := (7267)
      square := (191616930993427121154848440500000000000000)
      linear := (-19507625995871570570086573257901000000000000)
      constant := (510658486158777395420615875345128268764064874) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q27_52.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 22597
  qDenominator := 43472
  table := BinomialMassData.Q22597_43472.Degree098.table
  base := (8380736700393093407201194541309466421787/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 73820890000000000000000000000000000000000000000
      center := (634859654)
      previous := (317429827)
      next := (317429827)
      square := (8370019162723890079164934729480500000000000000)
      linear := (-853056048140235154431445261708739206000000000000)
      constant := (22354123379427778311140930512658946975618931730430) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q22597_43472.Degree098.checked
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
end ForestUnimodality.Stage80KernelData.Cell112.Kernel098
